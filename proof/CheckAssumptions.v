(* Reproduce the assumptions of the main theorem and alarm trace instance. *)
Require Import MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.
Require Import EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof.
Require Import OverlappingResponse_Example.
Require Import ZeroInit.
Require Import LTL_to_PBA_Final.

Check EncodingCorrect_proved.
Print Assumptions EncodingCorrect_proved.
Check canonical_encoding_all.
Print Assumptions canonical_encoding_all.
Check MTL_to_TBA_correct.
Print Assumptions MTL_to_TBA_correct.
Check MTL_to_TBA_correct_with.
Print Assumptions MTL_to_TBA_correct_with.
Check MTL_to_TBA_correct_with_zero_init.
Print Assumptions MTL_to_TBA_correct_with_zero_init.
Check alarm_response_tba_correct_with.
Print Assumptions alarm_response_tba_correct_with.
Check alarm_response_spot_backend_contract.
Print Assumptions alarm_response_spot_backend_contract.
Check alarm_response_spot_tba_correct.
Print Assumptions alarm_response_spot_tba_correct.
Check alarm_response_trace_violates.
Print Assumptions alarm_response_trace_violates.
Check alarm_overlap_trace_satisfies.
Print Assumptions alarm_overlap_trace_satisfies.
Check alarm_overlap_trace_accepted_by_spot_tba.
Print Assumptions alarm_overlap_trace_accepted_by_spot_tba.
Check alarm_response_trace_rejected_by_any_correct_backend.
Print Assumptions alarm_response_trace_rejected_by_any_correct_backend.
Check alarm_response_trace_rejected_by_spot_tba.
Print Assumptions alarm_response_trace_rejected_by_spot_tba.

(* Verified LTL-to-Buchi backend and the unconditional theorem. *)
Check LTL_TO_BUCHI_PROVED.
Print Assumptions LTL_TO_BUCHI_PROVED.
Check MTL_to_TBA_correct_verified.
Print Assumptions MTL_to_TBA_correct_verified.

(* Generalisation: abstract clocked-LTL theorem, MTL as an instance,
   a non-MTL instance, and polarity counterexamples. *)
Require Import ClockedLTL_Abstract.
Require Import ClockedLTL_Instance.
Require Import ClockedLTL_NonMTL.

Check ClockedLTL_Abstract.abstract_compile_correct.
Print Assumptions ClockedLTL_Abstract.abstract_compile_correct.
Check ClockedLTL_Instance.MTL_correct_via_abstract.
Print Assumptions ClockedLTL_Instance.MTL_correct_via_abstract.
Check gap_bound_instance.
Print Assumptions gap_bound_instance.
Check atom_ok_necessary_preservation.
Print Assumptions atom_ok_necessary_preservation.
Check atom_ok_necessary_restart.
Print Assumptions atom_ok_necessary_restart.
