import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.PiPartsRangeCheck
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.PiPartsRange
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Soundness.RhoRange.Tactic

namespace Keccak.Soundness
  #register_rho_normalize_4_input_range 400 3 0 0
  #register_rho_normalize_4_input_range 401 3 0 1
  #register_rho_normalize_4_input_range 402 3 0 2
  #register_rho_normalize_4_input_range 403 3 0 3
  #register_rho_normalize_4_input_range 404 3 0 4
  #register_rho_normalize_4_input_range 405 3 0 5
  #register_rho_normalize_4_input_range 406 3 0 6
  #register_rho_normalize_4_input_range 407 3 0 7
  #register_rho_normalize_4_input_range 456 3 0 8
  #register_rho_normalize_4_input_range 457 3 0 9
  #register_rho_normalize_4_input_range 458 3 0 10
  #register_rho_normalize_4_input_range 459 3 0 11
  #register_rho_normalize_4_input_range 460 3 0 12
  #register_rho_normalize_4_input_range 461 3 0 13
  #register_rho_normalize_4_input_range 462 3 0 14
  #register_rho_normalize_4_input_range 463 3 0 15
end Keccak.Soundness
