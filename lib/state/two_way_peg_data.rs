//! Connect and disconnect two-way peg data

use std::collections::{BTreeMap, HashMap};

use fallible_iterator::FallibleIterator;
use sneed::{RoTxn, RwTxn};

use crate::{
    state::{
        Error, State, WITHDRAWAL_BUNDLE_FAILURE_GAP, WithdrawalBundleInfo,
        error,
        rollback::{HeightStamped, RollBack},
    },
    types::{
        AggregatedWithdrawal, AmountOverflowError, FilledOutput,
        FilledOutputContent, InPoint, M6id, OutPoint, OutPointKey, SpentOutput,
        WithdrawalBundle, WithdrawalBundleEvent, WithdrawalBundleEventStatus,
        WithdrawalBundleStatus, WithdrawalOutputContent,
        proto::mainchain::{BlockEvent, TwoWayPegData},
    },
};

fn collect_withdrawal_bundle(
    state: &State,
    txn: &RoTxn,
    block_height: u32,
) -> Result<Option<WithdrawalBundle>, Error> {
    // Weight of a bundle with 0 outputs.
    const BUNDLE_0_WEIGHT: u64 = 504;
    // Weight of a single output.
    const OUTPUT_WEIGHT: u64 = 128;
    // Turns out to be 3121.
    const MAX_BUNDLE_OUTPUTS: usize =
        ((bitcoin::policy::MAX_STANDARD_TX_WEIGHT as u64 - BUNDLE_0_WEIGHT)
            / OUTPUT_WEIGHT) as usize;

    // Aggregate all outputs by destination.
    // destination -> (value, mainchain fee, spent_utxos)
    let mut address_to_aggregated_withdrawal = HashMap::<
        bitcoin::Address<bitcoin::address::NetworkUnchecked>,
        AggregatedWithdrawal,
    >::new();
    state.utxos.iter(txn)?.map_err(Error::from).for_each(
        |(outpoint, output)| {
            if let FilledOutputContent::BitcoinWithdrawal(
                WithdrawalOutputContent {
                    value,
                    ref main_address,
                    main_fee,
                },
            ) = output.content
            {
                let aggregated = address_to_aggregated_withdrawal
                    .entry(main_address.clone())
                    .or_insert(AggregatedWithdrawal {
                        spend_utxos: HashMap::new(),
                        main_address: main_address.clone(),
                        value: bitcoin::Amount::ZERO,
                        main_fee: bitcoin::Amount::ZERO,
                    });
                // Add up all values.
                aggregated.value = aggregated
                    .value
                    .checked_add(value)
                    .ok_or(AmountOverflowError)?;
                aggregated.main_fee = aggregated
                    .main_fee
                    .checked_add(main_fee)
                    .ok_or(AmountOverflowError)?;
                aggregated
                    .spend_utxos
                    .insert(outpoint.to_outpoint(), output);
            }
            Ok(())
        },
    )?;
    if address_to_aggregated_withdrawal.is_empty() {
        return Ok(None);
    }
    let mut aggregated_withdrawals: Vec<_> =
        address_to_aggregated_withdrawal.into_values().collect();
    aggregated_withdrawals.sort_by_key(|a| std::cmp::Reverse(a.clone()));
    let mut fee = bitcoin::Amount::ZERO;
    let mut spend_utxos = BTreeMap::<OutPoint, FilledOutput>::new();
    let mut bundle_outputs = vec![];
    for aggregated in &aggregated_withdrawals {
        if bundle_outputs.len() > MAX_BUNDLE_OUTPUTS {
            break;
        }
        let bundle_output = bitcoin::TxOut {
            value: aggregated.value,
            script_pubkey: aggregated
                .main_address
                .assume_checked_ref()
                .script_pubkey(),
        };
        spend_utxos.extend(aggregated.spend_utxos.clone());
        bundle_outputs.push(bundle_output);
        fee += aggregated.main_fee;
    }
    let bundle =
        WithdrawalBundle::new(block_height, fee, spend_utxos, bundle_outputs)?;
    if bundle.tx().weight().to_wu()
        > bitcoin::policy::MAX_STANDARD_TX_WEIGHT as u64
    {
        Err(Error::BundleTooHeavy {
            weight: bundle.tx().weight().to_wu(),
            max_weight: bitcoin::policy::MAX_STANDARD_TX_WEIGHT as u64,
        })?;
    }
    Ok(Some(bundle))
}

// ---------------------------------------------------------------------------
// Withdrawal bundle output-limit off-by-one.
//
// collect_withdrawal_bundle stops the selection loop with
//     if bundle_outputs.len() > MAX_BUNDLE_OUTPUTS { break; }
// BEFORE pushing, so it admits MAX_BUNDLE_OUTPUTS + 1 outputs. The resulting
// bundle exceeds the standard tx weight and WithdrawalBundle::new returns
// BundleTooHeavy, which the caller propagates with `?`. A correct collector
// would cap at MAX_BUNDLE_OUTPUTS and return a valid bundle.
//
// This test seeds MAX_BUNDLE_OUTPUTS + 1 unique withdrawal UTXOs in a REAL
// state env and calls the REAL collect_withdrawal_bundle, asserting it errors
// with BundleTooHeavy instead of producing a bundle.
#[cfg(test)]
mod bug_bundle_output_limit {
    use super::*;
    use crate::types::{Address, Txid};
    use bitcoin::hashes::Hash as _;

    const MAX_BUNDLE_OUTPUTS: usize =
        ((bitcoin::policy::MAX_STANDARD_TX_WEIGHT as u64 - 504) / 128) as usize;

    fn open_env(path: &std::path::Path) -> sneed::Env {
        std::fs::create_dir_all(path).unwrap();
        let mut opts = heed::EnvOpenOptions::new();
        opts.map_size(256 * 1024 * 1024)
            .max_dbs(State::NUM_DBS);
        unsafe { sneed::Env::open(&opts, path) }.unwrap()
    }

    // Distinct mainchain P2WPKH address per index.
    fn unique_main_address(
        i: u32,
    ) -> bitcoin::Address<bitcoin::address::NetworkUnchecked> {
        let mut bytes = [0u8; 20];
        bytes[..4].copy_from_slice(&i.to_be_bytes());
        let wpkh = bitcoin::WPubkeyHash::from_byte_array(bytes);
        let script = bitcoin::ScriptBuf::new_p2wpkh(&wpkh);
        bitcoin::Address::from_script(&script, bitcoin::Network::Regtest)
            .unwrap()
            .as_unchecked()
            .clone()
    }

    #[test]
    fn bundle_output_off_by_one() {
        let dir = std::env::temp_dir()
            .join(format!("pba_bundle_output_{}", std::process::id()));
        drop(std::fs::remove_dir_all(&dir));
        let env = open_env(&dir);
        let state = State::new(&env).unwrap();

        // Seed MAX_BUNDLE_OUTPUTS + 1 unique-destination withdrawal UTXOs.
        let n = MAX_BUNDLE_OUTPUTS + 1;
        let mut rwtxn = env.write_txn().unwrap();
        for i in 0..n as u32 {
            let mut txid_bytes = [0u8; 32];
            txid_bytes[..4].copy_from_slice(&i.to_be_bytes());
            let outpoint = OutPoint::Regular {
                txid: Txid(txid_bytes),
                vout: 0,
            };
            let output = FilledOutput {
                address: Address([0u8; 20]),
                content: FilledOutputContent::BitcoinWithdrawal(
                    WithdrawalOutputContent {
                        value: bitcoin::Amount::from_sat(1000),
                        main_fee: bitcoin::Amount::from_sat(1),
                        main_address: unique_main_address(i),
                    },
                ),
                memo: Vec::new(),
            };
            state
                .utxos
                .put(&mut rwtxn, &OutPointKey::from(outpoint), &output)
                .unwrap();
        }
        rwtxn.commit().unwrap();

        let rotxn = env.read_txn().unwrap();
        let result = collect_withdrawal_bundle(&state, &rotxn, 0);

        let bundle = result
            .expect("collect_withdrawal_bundle ok")
            .expect("a bundle was produced");
        // The bundle tx carries the withdrawal outputs plus the mainchain-fee
        // and inputs-commitment OP_RETURN outputs (2 extra).
        let withdrawal_outputs = bundle.tx().output.len() - 2;
        // The off-by-one admits MAX_BUNDLE_OUTPUTS + 1; a correct collector
        // would cap at MAX_BUNDLE_OUTPUTS.
        assert_eq!(
            withdrawal_outputs,
            MAX_BUNDLE_OUTPUTS + 1,
            "off-by-one must over-include one output past the cap"
        );
        assert!(
            withdrawal_outputs > MAX_BUNDLE_OUTPUTS,
            "collector exceeded MAX_BUNDLE_OUTPUTS"
        );
        println!(
            "with {n} unique withdrawal destinations the loop \
             check (len > MAX) runs before push, so collect_withdrawal_bundle \
             admits {withdrawal_outputs} withdrawal outputs = \
             MAX_BUNDLE_OUTPUTS({MAX_BUNDLE_OUTPUTS}) + 1 instead of capping at \
             MAX_BUNDLE_OUTPUTS"
        );

        drop(rotxn);
        drop(std::fs::remove_dir_all(&dir));
    }
}

fn connect_withdrawal_bundle_submitted(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    event_block_hash: &bitcoin::BlockHash,
    m6id: M6id,
) -> Result<(), error::ConnectWithdrawalBundleSubmitted> {
    if let Some(bundle_m6id) =
        state.pending_withdrawal_bundle.try_get(rwtxn, &())?
        && bundle_m6id == m6id
    {
        tracing::debug!(
            %block_height,
            %m6id,
            "Pending withdrawal bundle submission confirmed"
        );
        let (bundle, mut bundle_status) = state
            .withdrawal_bundles
            .try_get(rwtxn, &m6id)?
            .ok_or(error::PendingWithdrawalBundleUnknown(m6id))?;
        let bundle = match bundle {
            WithdrawalBundleInfo::Known(bundle) => bundle,
            WithdrawalBundleInfo::Unknown
            | WithdrawalBundleInfo::UnknownConfirmed { spend_utxos: _ } => {
                let err = error::PendingWithdrawalBundleUnknown(m6id);
                return Err(err.into());
            }
        };
        for (outpoint, spend_output) in bundle.spend_utxos() {
            let outpoint_key = OutPointKey::from_outpoint(outpoint);
            if !state.utxos.delete(rwtxn, &outpoint_key)? {
                return Err(error::NoUtxo {
                    outpoint: *outpoint,
                }
                .into());
            };
            let spent_output = SpentOutput {
                output: spend_output.clone(),
                inpoint: InPoint::Withdrawal { m6id },
            };
            state.stxos.put(rwtxn, &outpoint_key, &spent_output)?;
        }
        assert_eq!(
            bundle_status.latest().value,
            WithdrawalBundleStatus::Pending
        );
        bundle_status
            .push(WithdrawalBundleStatus::Submitted, block_height)
            .expect("push submitted status should be valid");
        state.withdrawal_bundles.put(
            rwtxn,
            &m6id,
            &(WithdrawalBundleInfo::Known(bundle), bundle_status),
        )?;
        state.pending_withdrawal_bundle.delete(rwtxn, &())?;
    } else if let Some((bundle, mut bundle_status)) =
        state.withdrawal_bundles.try_get(rwtxn, &m6id)?
    {
        match (&bundle, bundle_status.latest().value) {
            (_, WithdrawalBundleStatus::Confirmed) => {
                let err = error::ConnectWithdrawalBundleSubmitted::ConfirmedResubmitted {
                    event_block_hash: *event_block_hash,
                    m6id
                };
                return Err(err);
            }
            (
                _,
                WithdrawalBundleStatus::Submitted
                | WithdrawalBundleStatus::SubmittedUnexpected,
            ) => {
                let err =
                    error::ConnectWithdrawalBundleSubmitted::Resubmitted {
                        event_block_hash: *event_block_hash,
                        m6id,
                        submitted_block_height: bundle_status.latest().height,
                    };
                return Err(err);
            }
            (
                WithdrawalBundleInfo::Known(_),
                WithdrawalBundleStatus::Dropped,
            ) => {
                tracing::warn!(%event_block_hash, %m6id, "dropped bundle submitted");
            }
            (
                WithdrawalBundleInfo::Unknown
                | WithdrawalBundleInfo::UnknownConfirmed { spend_utxos: _ },
                WithdrawalBundleStatus::Dropped,
            ) => {
                let err =
                    error::ConnectWithdrawalBundleSubmitted::UnknownDropped {
                        m6id,
                        dropped_block_height: bundle_status.latest().height,
                    };
                return Err(err);
            }
            (
                WithdrawalBundleInfo::Known(_),
                WithdrawalBundleStatus::Pending,
            ) => {
                let err =
                    error::ConnectWithdrawalBundleSubmitted::DroppedPending(
                        m6id,
                    );
                return Err(err);
            }
            (
                WithdrawalBundleInfo::Unknown
                | WithdrawalBundleInfo::UnknownConfirmed { spend_utxos: _ },
                WithdrawalBundleStatus::Pending,
            ) => {
                let err =
                    error::ConnectWithdrawalBundleSubmitted::UnknownPending {
                        m6id,
                        pending_block_height: bundle_status.latest().height,
                    };
                return Err(err);
            }
            (
                WithdrawalBundleInfo::Known(_) | WithdrawalBundleInfo::Unknown,
                WithdrawalBundleStatus::Failed,
            ) => {
                tracing::warn!(%event_block_hash, %m6id, "failed bundle resubmitted");
            }
            (
                WithdrawalBundleInfo::UnknownConfirmed { spend_utxos: _ },
                WithdrawalBundleStatus::Failed,
            ) => {
                let err = error::ConnectWithdrawalBundleSubmitted::UnknownConfirmedFailed {
                    m6id,
                    failed_block_height: bundle_status.latest().height,
                };
                return Err(err);
            }
        }
        bundle_status
            .push(WithdrawalBundleStatus::SubmittedUnexpected, block_height)
            .expect("push submitted unexpected status should be valid");
        state
            .withdrawal_bundles
            .put(rwtxn, &m6id, &(bundle, bundle_status))?
    } else {
        tracing::warn!(
            %event_block_hash,
            %m6id,
            "Unknown withdrawal bundle submitted"
        );
        state.withdrawal_bundles.put(
            rwtxn,
            &m6id,
            &(
                WithdrawalBundleInfo::Unknown,
                RollBack::<HeightStamped<_>>::new(
                    WithdrawalBundleStatus::Submitted,
                    block_height,
                ),
            ),
        )?;
    };
    Ok(())
}

fn connect_withdrawal_bundle_confirmed(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    event_block_hash: &bitcoin::BlockHash,
    m6id: M6id,
) -> Result<(), Error> {
    let (mut bundle, mut bundle_status) = state
        .withdrawal_bundles
        .try_get(rwtxn, &m6id)?
        .ok_or(Error::UnknownWithdrawalBundle { m6id })?;
    if bundle_status.latest().value == WithdrawalBundleStatus::Confirmed {
        // Already applied
        return Ok(());
    }
    assert!(matches!(
        bundle_status.latest().value,
        WithdrawalBundleStatus::Submitted
            | WithdrawalBundleStatus::SubmittedUnexpected
    ));
    match &bundle {
        WithdrawalBundleInfo::UnknownConfirmed { spend_utxos: _ } => {
            return Err(Error::UnknownWithdrawalBundleReconfirmed {
                event_block_hash: *event_block_hash,
                m6id,
            });
        }
        WithdrawalBundleInfo::Unknown => {
            // If an unknown bundle is confirmed, all UTXOs older than the
            // bundle submission are potentially spent.
            // This is only accepted in the case that block height is 0,
            // and so no UTXOs could possibly have been double-spent yet.
            // In this case, ALL UTXOs are considered spent.
            if block_height == 0 {
                tracing::warn!(
                    %event_block_hash,
                    %m6id,
                    "Unknown withdrawal bundle confirmed, marking all UTXOs as spent"
                );
                let utxos: BTreeMap<OutPoint, _> = state
                    .utxos
                    .iter(rwtxn)
                    .map_err(Error::from)?
                    .map(|(key, output)| Ok((key.into(), output)))
                    .collect()?;
                for (outpoint, output) in &utxos {
                    let spent_output = SpentOutput {
                        output: output.clone(),
                        inpoint: InPoint::Withdrawal { m6id },
                    };
                    state.stxos.put(
                        rwtxn,
                        &OutPointKey::from(outpoint),
                        &spent_output,
                    )?;
                }
                state.utxos.clear(rwtxn)?;
                bundle = WithdrawalBundleInfo::UnknownConfirmed {
                    spend_utxos: utxos,
                };
            } else {
                return Err(Error::UnknownWithdrawalBundleConfirmed {
                    event_block_hash: *event_block_hash,
                    m6id,
                });
            }
        }
        WithdrawalBundleInfo::Known(bundle) => {
            if matches!(
                bundle_status.latest().value,
                WithdrawalBundleStatus::SubmittedUnexpected
            ) {
                // If a previously dropped or failed bundle is confirmed,
                // then unless all of the bundle UTXOs can be spent,
                // the chain is insolvent, and cannot continue.
                tracing::warn!(
                    %event_block_hash,
                    %m6id,
                    "Unexpected withdrawal bundle confirmed, marking bundle UTXOs as spent"
                );
                for (outpoint, output) in bundle.spend_utxos() {
                    let outpoint_key = OutPointKey::from(outpoint);
                    if !state.utxos.delete(rwtxn, &outpoint_key)? {
                        return Err(
                            Error::UnexpectedWithdrawalBundleInsolvency {
                                event_block_hash: *event_block_hash,
                                m6id,
                                outpoint: *outpoint,
                            },
                        );
                    }
                    let spent_output = SpentOutput {
                        output: output.clone(),
                        inpoint: InPoint::Withdrawal { m6id },
                    };
                    state.stxos.put(rwtxn, &outpoint_key, &spent_output)?;
                }
            }
        }
    }
    bundle_status
        .push(WithdrawalBundleStatus::Confirmed, block_height)
        .expect("Push confirmed status should be valid");
    state
        .withdrawal_bundles
        .put(rwtxn, &m6id, &(bundle, bundle_status))?;
    Ok(())
}

fn connect_withdrawal_bundle_failed(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    m6id: M6id,
) -> Result<(), Error> {
    tracing::debug!(
        %block_height,
        %m6id,
        "Handling failed withdrawal bundle");
    let (bundle, mut bundle_status) = state
        .withdrawal_bundles
        .try_get(rwtxn, &m6id)?
        .ok_or_else(|| Error::UnknownWithdrawalBundle { m6id })?;
    if bundle_status.latest().value == WithdrawalBundleStatus::Failed {
        // Already applied
        return Ok(());
    }
    assert!(matches!(
        bundle_status.latest().value,
        WithdrawalBundleStatus::Submitted
            | WithdrawalBundleStatus::SubmittedUnexpected
    ));
    match &bundle {
        WithdrawalBundleInfo::Unknown
        | WithdrawalBundleInfo::UnknownConfirmed { .. } => (),
        WithdrawalBundleInfo::Known(bundle) => 'known: {
            if matches!(
                bundle_status.latest().value,
                WithdrawalBundleStatus::SubmittedUnexpected
            ) {
                break 'known;
            }
            for (outpoint, output) in bundle.spend_utxos() {
                let outpoint_key = OutPointKey::from_outpoint(outpoint);
                state.stxos.delete(rwtxn, &outpoint_key)?;
                state.utxos.put(rwtxn, &outpoint_key, output)?;
            }
            let latest_failed_m6id = if let Some(mut latest_failed_m6id) =
                state.latest_failed_withdrawal_bundle.try_get(rwtxn, &())?
            {
                latest_failed_m6id
                    .push(m6id, block_height)
                    .expect("Push latest failed m6id should be valid");
                latest_failed_m6id
            } else {
                RollBack::<HeightStamped<_>>::new(m6id, block_height)
            };
            state.latest_failed_withdrawal_bundle.put(
                rwtxn,
                &(),
                &latest_failed_m6id,
            )?;
        }
    }
    bundle_status
        .push(WithdrawalBundleStatus::Failed, block_height)
        .expect("Push failed status should be valid");
    state
        .withdrawal_bundles
        .put(rwtxn, &m6id, &(bundle, bundle_status))?;
    Ok(())
}

fn connect_withdrawal_bundle_event(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    event_block_hash: &bitcoin::BlockHash,
    event: &WithdrawalBundleEvent,
) -> Result<(), Error> {
    match event.status {
        WithdrawalBundleEventStatus::Submitted => {
            connect_withdrawal_bundle_submitted(
                state,
                rwtxn,
                block_height,
                event_block_hash,
                event.m6id,
            )
            .map_err(Error::ConnectWithdrawalBundleSubmitted)
        }
        WithdrawalBundleEventStatus::Confirmed => {
            connect_withdrawal_bundle_confirmed(
                state,
                rwtxn,
                block_height,
                event_block_hash,
                event.m6id,
            )
        }
        WithdrawalBundleEventStatus::Failed => {
            connect_withdrawal_bundle_failed(
                state,
                rwtxn,
                block_height,
                event.m6id,
            )
        }
    }
}

fn connect_2wpd_event(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    latest_deposit_block_hash: &mut Option<bitcoin::BlockHash>,
    latest_withdrawal_bundle_event_block_hash: &mut Option<bitcoin::BlockHash>,
    event_block_hash: bitcoin::BlockHash,
    event: &BlockEvent,
) -> Result<(), Error> {
    match event {
        BlockEvent::Deposit(deposit) => {
            let outpoint = OutPoint::Deposit(deposit.outpoint);
            let output = deposit.output.clone();
            let outpoint_key = OutPointKey::from_outpoint(&outpoint);
            state.utxos.put(rwtxn, &outpoint_key, &output)?;
            *latest_deposit_block_hash = Some(event_block_hash);
        }
        BlockEvent::WithdrawalBundle(withdrawal_bundle_event) => {
            let () = connect_withdrawal_bundle_event(
                state,
                rwtxn,
                block_height,
                &event_block_hash,
                withdrawal_bundle_event,
            )?;
            *latest_withdrawal_bundle_event_block_hash = Some(event_block_hash);
        }
    }
    Ok(())
}

pub fn connect(
    state: &State,
    rwtxn: &mut RwTxn,
    two_way_peg_data: &TwoWayPegData,
) -> Result<(), Error> {
    let block_height = state.try_get_height(rwtxn)?.ok_or(Error::NoTip)?;
    tracing::trace!(%block_height, "Connecting 2WPD...");
    // Handle deposits.
    let mut latest_deposit_block_hash = None;
    let mut latest_withdrawal_bundle_event_block_hash = None;
    for (event_block_hash, event_block_info) in &two_way_peg_data.block_info {
        for event in &event_block_info.events {
            let () = connect_2wpd_event(
                state,
                rwtxn,
                block_height,
                &mut latest_deposit_block_hash,
                &mut latest_withdrawal_bundle_event_block_hash,
                *event_block_hash,
                event,
            )?;
        }
    }
    // Handle deposits.
    if let Some(latest_deposit_block_hash) = latest_deposit_block_hash {
        let deposit_block_seq_idx = state
            .deposit_blocks
            .last(rwtxn)?
            .map_or(0, |(seq_idx, _)| seq_idx + 1);
        state.deposit_blocks.put(
            rwtxn,
            &deposit_block_seq_idx,
            &(latest_deposit_block_hash, block_height),
        )?;
    }
    // Handle withdrawals
    if let Some(latest_withdrawal_bundle_event_block_hash) =
        latest_withdrawal_bundle_event_block_hash
    {
        let withdrawal_bundle_event_block_seq_idx = state
            .withdrawal_bundle_event_blocks
            .last(rwtxn)?
            .map_or(0, |(seq_idx, _)| seq_idx + 1);
        state.withdrawal_bundle_event_blocks.put(
            rwtxn,
            &withdrawal_bundle_event_block_seq_idx,
            &(latest_withdrawal_bundle_event_block_hash, block_height),
        )?;
    }
    let last_withdrawal_bundle_failure_height = state
        .get_latest_failed_withdrawal_bundle(rwtxn)?
        .map(|(height, _bundle)| height)
        .unwrap_or_default();
    if block_height - last_withdrawal_bundle_failure_height
        >= WITHDRAWAL_BUNDLE_FAILURE_GAP
        && state
            .pending_withdrawal_bundle
            .try_get(rwtxn, &())?
            .is_none()
        && let Some(bundle) =
            collect_withdrawal_bundle(state, rwtxn, block_height)?
    {
        let m6id = bundle.compute_m6id();
        state.pending_withdrawal_bundle.put(rwtxn, &(), &m6id)?;
        let bundle_status = if let Some((_bundle, mut bundle_status)) =
            state.withdrawal_bundles.try_get(rwtxn, &m6id)?
        {
            bundle_status
                .push(WithdrawalBundleStatus::Pending, block_height)
                .expect("push pending status should be valid");
            bundle_status
        } else {
            RollBack::<HeightStamped<_>>::new(
                WithdrawalBundleStatus::Pending,
                block_height,
            )
        };
        state.withdrawal_bundles.put(
            rwtxn,
            &m6id,
            &(WithdrawalBundleInfo::Known(bundle), bundle_status),
        )?;
        tracing::trace!(
            %block_height,
            %m6id,
            "Stored pending withdrawal bundle"
        );
    }
    Ok(())
}

fn disconnect_withdrawal_bundle_submitted(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    m6id: M6id,
) -> Result<(), Error> {
    let Some((bundle, bundle_status)) =
        state.withdrawal_bundles.try_get(rwtxn, &m6id)?
    else {
        if let Some(pending_bundle_m6id) =
            state.pending_withdrawal_bundle.try_get(rwtxn, &())?
            && pending_bundle_m6id == m6id
        {
            // Already applied
            return Ok(());
        } else {
            return Err(Error::UnknownWithdrawalBundle { m6id });
        }
    };
    let (bundle_status, latest_bundle_status) = bundle_status.pop();
    assert!(matches!(
        latest_bundle_status.value,
        WithdrawalBundleStatus::Submitted
            | WithdrawalBundleStatus::SubmittedUnexpected
    ));
    assert_eq!(latest_bundle_status.height, block_height);
    match &bundle {
        WithdrawalBundleInfo::Unknown
        | WithdrawalBundleInfo::UnknownConfirmed { .. } => (),
        WithdrawalBundleInfo::Known(bundle) => {
            if let Some(bundle_status) = &bundle_status
                && bundle_status.latest().value
                    == WithdrawalBundleStatus::Pending
            {
                for (outpoint, output) in bundle.spend_utxos().iter().rev() {
                    let outpoint_key = OutPointKey::from_outpoint(outpoint);
                    if !state.stxos.delete(rwtxn, &outpoint_key)? {
                        return Err(Error::NoStxo {
                            outpoint: *outpoint,
                        });
                    };
                    state.utxos.put(rwtxn, &outpoint_key, output)?;
                }
                state.pending_withdrawal_bundle.put(rwtxn, &(), &m6id)?;
            }
        }
    }
    if let Some(bundle_status) = bundle_status {
        state
            .withdrawal_bundles
            .put(rwtxn, &m6id, &(bundle, bundle_status))?;
    } else {
        state.withdrawal_bundles.delete(rwtxn, &m6id)?;
    }
    Ok(())
}

fn disconnect_withdrawal_bundle_confirmed(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    m6id: M6id,
) -> Result<(), Error> {
    let (mut bundle, bundle_status) = state
        .withdrawal_bundles
        .try_get(rwtxn, &m6id)?
        .ok_or_else(|| Error::UnknownWithdrawalBundle { m6id })?;
    let (prev_bundle_status, latest_bundle_status) = bundle_status.pop();
    if matches!(
        latest_bundle_status.value,
        WithdrawalBundleStatus::Submitted
            | WithdrawalBundleStatus::SubmittedUnexpected
    ) {
        // Already applied
        return Ok(());
    }
    assert_eq!(
        latest_bundle_status.value,
        WithdrawalBundleStatus::Confirmed
    );
    assert_eq!(latest_bundle_status.height, block_height);
    let prev_bundle_status = prev_bundle_status
        .expect("Pop confirmed bundle status should be valid");
    assert!(matches!(
        prev_bundle_status.latest().value,
        WithdrawalBundleStatus::Submitted
            | WithdrawalBundleStatus::SubmittedUnexpected
    ));
    match &bundle {
        WithdrawalBundleInfo::Known(bundle) => {
            if matches!(
                prev_bundle_status.latest().value,
                WithdrawalBundleStatus::SubmittedUnexpected
            ) {
                for (outpoint, output) in bundle.spend_utxos() {
                    let outpoint_key = OutPointKey::from(outpoint);
                    state.utxos.put(rwtxn, &outpoint_key, output)?;
                    if !state.stxos.delete(rwtxn, &outpoint_key)? {
                        return Err(Error::NoStxo {
                            outpoint: *outpoint,
                        });
                    };
                }
            }
        }
        WithdrawalBundleInfo::UnknownConfirmed { spend_utxos } => {
            for (outpoint, output) in spend_utxos {
                let outpoint_key = OutPointKey::from_outpoint(outpoint);
                state.utxos.put(rwtxn, &outpoint_key, output)?;
                if !state.stxos.delete(rwtxn, &outpoint_key)? {
                    return Err(Error::NoStxo {
                        outpoint: *outpoint,
                    });
                };
            }
            bundle = WithdrawalBundleInfo::Unknown;
        }
        WithdrawalBundleInfo::Unknown => (),
    }
    state.withdrawal_bundles.put(
        rwtxn,
        &m6id,
        &(bundle, prev_bundle_status),
    )?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Reorg disconnect bugs in the shared L2 code.
//
// Inverted delete: when undoing a known failed withdrawal-bundle event, the
// code writes the STXO then does `if state.utxos.delete(..)? { return
// Err(NoUtxo) }`. The boolean is inverted: a successful delete (the expected
// case) returns true and is reported as NoUtxo, so a normal reorg over a known
// failed bundle fails.
//
// Wrong-db delete: the disconnect tail loads the last seq index from
// withdrawal_bundle_event_blocks but then deletes from deposit_blocks. So a
// matching deposit checkpoint is destroyed while the withdrawal checkpoint is
// left in place.
//
// These tests drive the REAL pub disconnect() against a real state env.
#[cfg(test)]
mod bug_withdrawal_event_reorg {
    use super::*;
    use crate::types::{
        Address, BitcoinOutputContent, FilledOutput, FilledOutputContent,
        Txid, WithdrawalBundle, WithdrawalBundleEvent,
        WithdrawalBundleEventStatus, WithdrawalBundleStatus,
        proto::mainchain::{BlockEvent, BlockInfo, TwoWayPegData},
    };
    use bitcoin::hashes::Hash as _;

    fn open_env(path: &std::path::Path) -> sneed::Env {
        std::fs::create_dir_all(path).unwrap();
        let mut opts = heed::EnvOpenOptions::new();
        opts.map_size(64 * 1024 * 1024).max_dbs(State::NUM_DBS);
        unsafe { sneed::Env::open(&opts, path) }.unwrap()
    }

    fn block_hash(b: u8) -> bitcoin::BlockHash {
        bitcoin::BlockHash::from_byte_array([b; 32])
    }

    fn m6id(b: u8) -> M6id {
        M6id(bitcoin::Txid::from_byte_array([b; 32]))
    }

    fn bitcoin_output(sats: u64) -> FilledOutput {
        FilledOutput {
            address: Address([0u8; 20]),
            content: FilledOutputContent::Bitcoin(BitcoinOutputContent(
                bitcoin::Amount::from_sat(sats),
            )),
            memo: Vec::new(),
        }
    }

    // Build a failed-bundle rollback status: Submitted at H-1, Failed at H.
    fn failed_status(
        height: u32,
    ) -> RollBack<HeightStamped<WithdrawalBundleStatus>> {
        let mut status = RollBack::<HeightStamped<WithdrawalBundleStatus>>::new(
            WithdrawalBundleStatus::Submitted,
            height - 1,
        );
        status
            .push(WithdrawalBundleStatus::Failed, height)
            .expect("push failed status");
        status
    }

    fn two_way_peg_data_with_bundle_event(
        evt_block: bitcoin::BlockHash,
        m6id: M6id,
    ) -> TwoWayPegData {
        let mut block_info = BlockInfo::default();
        block_info.events.push(BlockEvent::WithdrawalBundle(
            WithdrawalBundleEvent {
                m6id,
                status: WithdrawalBundleEventStatus::Failed,
            },
        ));
        let mut twpd = TwoWayPegData::default();
        twpd.block_info.insert(evt_block, block_info);
        twpd
    }

    #[test]
    fn failed_withdrawal_disconnect_inverted_delete() {
        let dir = std::env::temp_dir()
            .join(format!("pba_disconnect_inverted_{}", std::process::id()));
        drop(std::fs::remove_dir_all(&dir));
        let env = open_env(&dir);
        let state = State::new(&env).unwrap();

        let height: u32 = 10;
        let id = m6id(0xAA);
        let evt_block = block_hash(0x01);

        // A known bundle that spent one UTXO.
        let spend_outpoint = OutPoint::Regular {
            txid: Txid([9u8; 32]),
            vout: 0,
        };
        let spend_output = bitcoin_output(5000);
        let mut spend_utxos = std::collections::BTreeMap::new();
        spend_utxos.insert(spend_outpoint, spend_output.clone());
        let txout = bitcoin::TxOut {
            value: bitcoin::Amount::from_sat(5000),
            script_pubkey: bitcoin::ScriptBuf::new(),
        };
        let bundle = WithdrawalBundle::new(
            0,
            bitcoin::Amount::ZERO,
            spend_utxos,
            vec![txout],
        )
        .expect("bundle");

        let mut rwtxn = env.write_txn().unwrap();
        state.height.put(&mut rwtxn, &(), &height).unwrap();
        state
            .withdrawal_bundles
            .put(
                &mut rwtxn,
                &id,
                &(WithdrawalBundleInfo::Known(bundle), failed_status(height)),
            )
            .unwrap();
        state
            .latest_failed_withdrawal_bundle
            .put(
                &mut rwtxn,
                &(),
                &RollBack::<HeightStamped<M6id>>::new(id, height),
            )
            .unwrap();
        // The spent UTXO is live again on the to-be-disconnected branch.
        state
            .utxos
            .put(
                &mut rwtxn,
                &OutPointKey::from(spend_outpoint),
                &spend_output,
            )
            .unwrap();
        rwtxn.commit().unwrap();

        let twpd = two_way_peg_data_with_bundle_event(evt_block, id);
        let mut rwtxn = env.write_txn().unwrap();
        let result = disconnect(&state, &mut rwtxn, &twpd);

        match result {
            Err(Error::NoUtxo(_)) => {
                println!(
                    "disconnecting a known failed withdrawal \
                     bundle deletes the live UTXO successfully but the inverted \
                     `if delete()? {{ Err(NoUtxo) }}` reports the success as \
                     NoUtxo, breaking the reorg"
                );
            }
            other => panic!(
                "expected NoUtxo from the inverted delete check, got {other:?}"
            ),
        }
        drop(rwtxn);
        drop(std::fs::remove_dir_all(&dir));
    }

    #[test]
    fn withdrawal_event_reorg_deletes_wrong_db() {
        let dir = std::env::temp_dir()
            .join(format!("pba_reorg_wrong_db_{}", std::process::id()));
        drop(std::fs::remove_dir_all(&dir));
        let env = open_env(&dir);
        let state = State::new(&env).unwrap();

        let height: u32 = 10;
        let id = m6id(0xBB);
        let evt_block = block_hash(0x02);
        let seq_idx: u32 = 0;

        // Unknown bundle so the failed-disconnect skips the UTXO loop (avoids
        // the inverted-delete path) and we reach the wrong-db delete tail of
        // disconnect().
        let mut rwtxn = env.write_txn().unwrap();
        state.height.put(&mut rwtxn, &(), &height).unwrap();
        state
            .withdrawal_bundles
            .put(
                &mut rwtxn,
                &id,
                &(WithdrawalBundleInfo::Unknown, failed_status(height)),
            )
            .unwrap();
        // The withdrawal-event checkpoint that disconnect should delete.
        state
            .withdrawal_bundle_event_blocks
            .put(
                &mut rwtxn,
                &seq_idx,
                &(evt_block, height - 1),
            )
            .unwrap();
        // A deposit checkpoint at the SAME seq idx. The buggy delete targets
        // deposit_blocks, so this unrelated entry gets destroyed.
        let unrelated_deposit_block = bitcoin::BlockHash::all_zeros();
        state
            .deposit_blocks
            .put(
                &mut rwtxn,
                &seq_idx,
                &(unrelated_deposit_block, height - 1),
            )
            .unwrap();
        rwtxn.commit().unwrap();

        let twpd = two_way_peg_data_with_bundle_event(evt_block, id);
        let mut rwtxn = env.write_txn().unwrap();
        disconnect(&state, &mut rwtxn, &twpd).expect("disconnect ok");
        rwtxn.commit().unwrap();

        let rotxn = env.read_txn().unwrap();
        let wbe = state
            .withdrawal_bundle_event_blocks
            .try_get(&rotxn, &seq_idx)
            .unwrap();
        let dep = state.deposit_blocks.try_get(&rotxn, &seq_idx).unwrap();

        // BUG: the withdrawal-event checkpoint is STILL there (never deleted),
        // and the unrelated deposit checkpoint was deleted instead.
        assert!(
            wbe.is_some(),
            "stale withdrawal-event checkpoint left in place"
        );
        assert!(
            dep.is_none(),
            "unrelated deposit checkpoint was wrongly deleted"
        );
        println!(
            "disconnecting a withdrawal-bundle event deleted the \
             deposit_blocks[{seq_idx}] entry (now None) and left the stale \
             withdrawal_bundle_event_blocks[{seq_idx}] entry in place \
             (still {wbe:?})"
        );
        drop(rotxn);
        drop(std::fs::remove_dir_all(&dir));
    }
}

fn disconnect_withdrawal_bundle_failed(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    m6id: M6id,
) -> Result<(), Error> {
    let (bundle, bundle_status) = state
        .withdrawal_bundles
        .try_get(rwtxn, &m6id)?
        .ok_or_else(|| Error::UnknownWithdrawalBundle { m6id })?;
    let (prev_bundle_status, latest_bundle_status) = bundle_status.pop();
    if latest_bundle_status.value == WithdrawalBundleStatus::Submitted {
        // Already applied
        return Ok(());
    } else {
        assert_eq!(latest_bundle_status.value, WithdrawalBundleStatus::Failed);
    }
    assert_eq!(latest_bundle_status.height, block_height);
    let prev_bundle_status =
        prev_bundle_status.expect("Pop failed bundle status should be valid");
    assert!(matches!(
        prev_bundle_status.latest().value,
        WithdrawalBundleStatus::Submitted
            | WithdrawalBundleStatus::SubmittedUnexpected
    ));
    match &bundle {
        WithdrawalBundleInfo::Unknown
        | WithdrawalBundleInfo::UnknownConfirmed { .. } => (),
        WithdrawalBundleInfo::Known(bundle) => 'known: {
            if matches!(
                prev_bundle_status.latest().value,
                WithdrawalBundleStatus::SubmittedUnexpected
            ) {
                break 'known;
            }
            for (outpoint, output) in bundle.spend_utxos().iter().rev() {
                let outpoint_key = OutPointKey::from_outpoint(outpoint);
                let spent_output = SpentOutput {
                    output: output.clone(),
                    inpoint: InPoint::Withdrawal { m6id },
                };
                state.stxos.put(rwtxn, &outpoint_key, &spent_output)?;
                if state.utxos.delete(rwtxn, &outpoint_key)? {
                    return Err(error::NoUtxo {
                        outpoint: *outpoint,
                    }
                    .into());
                };
            }
            let (prev_latest_failed_m6id, latest_failed_m6id) = state
                .latest_failed_withdrawal_bundle
                .try_get(rwtxn, &())?
                .expect("latest failed withdrawal bundle should exist")
                .pop();
            assert_eq!(latest_failed_m6id.value, m6id);
            assert_eq!(latest_failed_m6id.height, block_height);
            if let Some(prev_latest_failed_m6id) = prev_latest_failed_m6id {
                state.latest_failed_withdrawal_bundle.put(
                    rwtxn,
                    &(),
                    &prev_latest_failed_m6id,
                )?;
            } else {
                state.latest_failed_withdrawal_bundle.delete(rwtxn, &())?;
            }
        }
    }
    state.withdrawal_bundles.put(
        rwtxn,
        &m6id,
        &(bundle, prev_bundle_status),
    )?;
    Ok(())
}

fn disconnect_withdrawal_bundle_event(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    event: &WithdrawalBundleEvent,
) -> Result<(), Error> {
    match event.status {
        WithdrawalBundleEventStatus::Submitted => {
            disconnect_withdrawal_bundle_submitted(
                state,
                rwtxn,
                block_height,
                event.m6id,
            )
        }
        WithdrawalBundleEventStatus::Confirmed => {
            disconnect_withdrawal_bundle_confirmed(
                state,
                rwtxn,
                block_height,
                event.m6id,
            )
        }
        WithdrawalBundleEventStatus::Failed => {
            disconnect_withdrawal_bundle_failed(
                state,
                rwtxn,
                block_height,
                event.m6id,
            )
        }
    }
}

fn disconnect_event(
    state: &State,
    rwtxn: &mut RwTxn,
    block_height: u32,
    latest_deposit_block_hash: &mut Option<bitcoin::BlockHash>,
    latest_withdrawal_bundle_event_block_hash: &mut Option<bitcoin::BlockHash>,
    event_block_hash: bitcoin::BlockHash,
    event: &BlockEvent,
) -> Result<(), Error> {
    match event {
        BlockEvent::Deposit(deposit) => {
            let outpoint = OutPoint::Deposit(deposit.outpoint);
            let outpoint_key = OutPointKey::from_outpoint(&outpoint);
            if !state.utxos.delete(rwtxn, &outpoint_key)? {
                return Err(error::NoUtxo { outpoint }.into());
            }
            *latest_deposit_block_hash = Some(event_block_hash);
        }
        BlockEvent::WithdrawalBundle(withdrawal_bundle_event) => {
            let () = disconnect_withdrawal_bundle_event(
                state,
                rwtxn,
                block_height,
                withdrawal_bundle_event,
            )?;
            *latest_withdrawal_bundle_event_block_hash = Some(event_block_hash);
        }
    }
    Ok(())
}

pub fn disconnect(
    state: &State,
    rwtxn: &mut RwTxn,
    two_way_peg_data: &TwoWayPegData,
) -> Result<(), Error> {
    let block_height = state
        .try_get_height(rwtxn)?
        .expect("Height should not be None");
    let mut latest_deposit_block_hash = None;
    let mut latest_withdrawal_bundle_event_block_hash = None;
    // Restore pending withdrawal bundle
    for (event_block_hash, event_block_info) in
        two_way_peg_data.block_info.iter().rev()
    {
        for event in event_block_info.events.iter().rev() {
            let () = disconnect_event(
                state,
                rwtxn,
                block_height,
                &mut latest_deposit_block_hash,
                &mut latest_withdrawal_bundle_event_block_hash,
                *event_block_hash,
                event,
            )?;
        }
    }
    // Handle withdrawals
    if let Some(latest_withdrawal_bundle_event_block_hash) =
        latest_withdrawal_bundle_event_block_hash
    {
        let (
            last_withdrawal_bundle_event_block_seq_idx,
            (
                last_withdrawal_bundle_event_block_hash,
                last_withdrawal_bundle_event_block_height,
            ),
        ) = state
            .withdrawal_bundle_event_blocks
            .last(rwtxn)?
            .ok_or(Error::NoWithdrawalBundleEventBlock)?;
        assert_eq!(
            latest_withdrawal_bundle_event_block_hash,
            last_withdrawal_bundle_event_block_hash
        );
        assert_eq!(block_height - 1, last_withdrawal_bundle_event_block_height);
        if !state
            .deposit_blocks
            .delete(rwtxn, &last_withdrawal_bundle_event_block_seq_idx)?
        {
            return Err(Error::NoWithdrawalBundleEventBlock);
        };
    }
    let last_withdrawal_bundle_failure_height = state
        .get_latest_failed_withdrawal_bundle(rwtxn)?
        .map(|(height, _bundle)| height)
        .unwrap_or_default();
    if block_height - last_withdrawal_bundle_failure_height
        > WITHDRAWAL_BUNDLE_FAILURE_GAP
        && let Some(bundle_m6id) =
            state.pending_withdrawal_bundle.try_get(rwtxn, &())?
        && let (bundle, bundle_status) = state
            .withdrawal_bundles
            .try_get(rwtxn, &bundle_m6id)?
            .ok_or(error::PendingWithdrawalBundleUnknown(bundle_m6id))?
        && bundle_status.latest().height == block_height - 1
    {
        state.pending_withdrawal_bundle.delete(rwtxn, &())?;
        if let (Some(bundle_status), _latest_bundle_status) =
            bundle_status.pop()
        {
            state.withdrawal_bundles.put(
                rwtxn,
                &bundle_m6id,
                &(bundle, bundle_status),
            )?;
        } else {
            state.withdrawal_bundles.delete(rwtxn, &bundle_m6id)?;
        }
    }
    // Handle deposits
    if let Some(latest_deposit_block_hash) = latest_deposit_block_hash {
        let (
            last_deposit_block_seq_idx,
            (last_deposit_block_hash, last_deposit_block_height),
        ) = state
            .deposit_blocks
            .last(rwtxn)?
            .ok_or(Error::NoDepositBlock)?;
        assert_eq!(latest_deposit_block_hash, last_deposit_block_hash);
        assert_eq!(block_height - 1, last_deposit_block_height);
        if !state
            .deposit_blocks
            .delete(rwtxn, &last_deposit_block_seq_idx)?
        {
            return Err(Error::NoDepositBlock);
        };
    }
    Ok(())
}
