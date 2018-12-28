// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Parity.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

//! Metrics for parity ethereum executables

//#![nightly]
#![feature(proc_macro_hygiene)] // TODO proc_macro_hack ? or revert to xtra verbose std macro

pub extern crate metrics_backends;

pub use metrics_backends::*;
pub use metrics_backends::metrics_derive::*;

#[metrics_modules(pro,slogger)]
struct MetricStates {
	a_int_counter: Counter,
  insert_timer: Timer,
  get_timer: Timer,
  statedb_load_bloom: Timer,
  statedb_commit_bloom: Timer,
  statedb_journal_under: Timer,
  statedb_sync_cache: Timer,
  statedb_mem_used: Timer,
  statedb_is_allowed: Timer,
  statedb_get_cached_account: Timer,
  statedb_get_cached_code: Timer,
  statedb_get_cached: Timer,
  statedb_cach_account: Timer,
  statedb_cach_code: Timer,
  statedb_cach: Timer,
}

#[macro_export]
macro_rules! mets {
	(fast_only, $($exp:tt)*) => {
		$crate::metrics_backends::metrics_derive::metrics!(from_crate(metrics) [pro], $($exp)*)
	};
	($($exp:tt)*) => {
		$crate::metrics_backends::metrics_derive::metrics!(from_crate(metrics) [pro, slogger], $($exp)*)
	};
}

#[macro_export]
macro_rules! timer_enclose_backends {
  ($($exp:tt)*) => {
    $crate::metrics_backends::metrics_derive::metrics!(from_crate(metrics) [pro], $($exp)*)
  };
}

#[macro_export]
macro_rules! timer_enclose_backends_alt {
  ($($exp:tt)*) => {
    $crate::metrics_backends::metrics_derive::metrics!(from_crate(metrics) [pro, slogger], $($exp)*)
  };
}
