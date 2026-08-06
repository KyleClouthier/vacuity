// GENERATED VACUITY PROBES. Each havocs the inputs and the result and asserts one
// postcondition. VERIFICATION SUCCESS MEANS THE CLAUSE IS VACUOUS: it holds for every
// value the return type admits, so every implementation satisfies it and proving it
// establishes nothing. Failure is the healthy outcome.
#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
pub mod vacuity_probes {
    use super::*;

    /// Probes `new_unchecked` clause 0. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_new_unchecked_1() {
        let align: usize = kani::any();
        let probe_result: Alignment = kani::any();
        let result = &probe_result;
        assert!(result . as_usize () == align);
    }

    /// Probes `new_unchecked` clause 1. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_new_unchecked_2() {
        let align: usize = kani::any();
        let probe_result: Alignment = kani::any();
        let result = &probe_result;
        assert!(result . as_usize () . is_power_of_two ());
    }

    /// Probes `as_usize` clause 0. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_as_usize_3() {
        let probe_self: Alignment = kani::any();
        let probe_result: usize = kani::any();
        let result = &probe_result;
        assert!(result . is_power_of_two ());
    }

    /// Probes `as_nonzero` clause 0. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_as_nonzero_4() {
        let probe_self: Alignment = kani::any();
        let probe_result: NonZero < usize > = kani::any();
        let result = &probe_result;
        assert!(result . get () . is_power_of_two ());
    }

    /// Probes `as_nonzero` clause 1. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_as_nonzero_5() {
        let probe_self: Alignment = kani::any();
        let probe_result: NonZero < usize > = kani::any();
        let result = &probe_result;
        assert!(result . get () == probe_self . as_usize ());
    }

    /// Probes `log2` clause 0. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_log2_6() {
        let probe_self: Alignment = kani::any();
        let probe_result: u32 = kani::any();
        let result = &probe_result;
        assert!((* result as usize) < mem :: size_of :: < usize > () * 8);
    }

    /// Probes `log2` clause 1. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_log2_7() {
        let probe_self: Alignment = kani::any();
        let probe_result: u32 = kani::any();
        let result = &probe_result;
        assert!(1usize << * result == probe_self . as_usize ());
    }

    /// Probes `mask` clause 0. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_mask_8() {
        let probe_self: Alignment = kani::any();
        let probe_result: usize = kani::any();
        let result = &probe_result;
        assert!(* result > 0);
    }

    /// Probes `mask` clause 1. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_mask_9() {
        let probe_self: Alignment = kani::any();
        let probe_result: usize = kani::any();
        let result = &probe_result;
        assert!(* result == ! (probe_self . as_usize () - 1));
    }

    /// Probes `mask` clause 2. SUCCESS means the clause is VACUOUS.
    #[kani::proof]
    fn probe_vacuity_mask_10() {
        let probe_self: Alignment = kani::any();
        let probe_result: usize = kani::any();
        let result = &probe_result;
        assert!(probe_self . as_usize () & * result == probe_self . as_usize ());
    }

}
