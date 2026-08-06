# vacuity

Some postconditions prove nothing at all.

```rust
#[ensures(|result| result.get() > 0)]
pub const fn count_ones(self) -> NonZero<u32>
```

The return type is `NonZero<u32>`. Its invariant is already non-zero. So that clause holds
for **every implementation that could ever be written**, including one that ignores its
input and returns `1`. The proof passes. It establishes nothing.

No reachability analysis finds this, because nothing is unreachable. The assertion runs,
the harness is healthy, the verdict is correct. The clause is the problem.

`vacuity` decides it, one query per clause.

## Use

```console
$ vacuity ./src --out probes.rs
  postconditions found : 13
  probes generated     : 10
  skipped              : 2

$ # paste probes.rs into the crate under test
$ cargo kani --harness probe_vacuity_ > out.txt

$ vacuity ./src --results out.txt
  1 clauses are PROVEN VACUOUS.
  Each holds for every value its return type admits, so every
  implementation satisfies it and proving it establishes nothing.

    src/ptr/alignment.rs:95  new_unchecked
```

**Verification success is the bug report.** Failure is the healthy outcome: it produces a
type-valid value your clause rejects, proving the clause constrains something.

Exit 1 when anything is vacuous, so this works as a CI gate on new contracts.

## Install

```console
cargo install vacuity
```

No prebuilt binaries on purpose. It reads your code, so you should be able to read its
source first. Two dependencies, no network, no database, no telemetry.

## Why one query is enough

A probe replaces the function body with an arbitrary value of its return type and asserts
the clause against it. That looks like a sample. It is not.

```lean
theorem havoc_decides_vacuity (I : B → Prop) (P : A → B → Prop) :
    Vacuous I P ↔ ∀ g : A → B, TypeValid I g → Satisfies P g
```

The right-hand side quantifies over **every type-valid implementation anyone could
write**. The left is the single query. They are equivalent, and the hard direction is one
line: for any admissible value `b`, the constant function returning `b` is itself a
type-valid implementation, so it already lies inside the quantifier.

The proof is in [`lean/Vacuity.lean`](lean/Vacuity.lean), machine-checked, no `sorry`, no
external libraries. Three of its seven theorems depend on no axioms at all.

## Compared to writing mutants

Mutation testing answers this by hand: break the function, see whether the proof notices.

|  | mutation | probe |
|---|---|---|
| queries | one build per mutant | one per clause |
| on success | **nothing learned** | vacuous, proved |
| on failure | not vacuous | not vacuous, with a witness |
| needs a working harness | yes | **no** |

That last row is not a technicality. `Alignment::of` in the Rust standard library has its
harness disabled behind [kani#3905](https://github.com/model-checking/kani/issues/3905),
and its clause was still decided, because the probe never calls the function. You can
check a specification before you can check the code.

## What it skips, and why it tells you

A clause is probeable only when every type involved can be produced by `kani::any()`.
Generics, raw pointers, references and unknown user types cannot be, and **every skip is
printed with its reason**:

```
  --- not probed, with reasons ---
    1  generic function, no type arguments to instantiate
       of
    1  return type: `Self` has no kani::Arbitrary this tool can see
       new
```

A generator that quietly emitted fewer probes than there are clauses would report a clean
bill of health for clauses it never read. Likewise, a probe missing from the Kani output is
reported as **unknown**, never as passing, and exits 2.

Hand-written `impl kani::Arbitrary for T` blocks are detected, so your domain types count.

## The assumption this rests on

A probe replaces the result with `kani::any::<ReturnType>()`. That substitution is only
legitimate if **`kani::any` can produce every value the function could actually return**.

The two ways that can fail are not symmetric, and the asymmetry is the reason this is
usable at all:

| if `Arbitrary` produces | effect | direction |
|---|---|---|
| more values than the function can return | the clause is tested against unreachable values, fails more often | **under-reports**: misses vacuous clauses, invents nothing |
| fewer values than the function can return | a reachable counterexample is never generated | **over-reports**: calls a clause vacuous when it is not |

Only the second is dangerous, because a false claim about someone's contract costs more
than every true one it might find. So: **a hand-written `impl kani::Arbitrary` that does
not cover its type can make this tool wrong.** Derived instances and the standard ones are
fine. If you wrote a narrow one, this will trust it.

The general condition is proved in [`lean/Collapse.lean`](lean/Collapse.lean): substituting
outcomes for systems is valid for every claim exactly when the generator class is
*pointwise surjective* onto the admissible set, meaning every admissible value is
producible at every input. Constants give that for free, which is why it works for ordinary
per-call postconditions. It stops working when some admissible outcome is unreachable, and
the same file constructs the claim that separates the two checks when it does.

## Limits

- **Vacuous is not the same as weak.** `Alignment::as_usize` probes as having content, and
  its clause is still thin. This decides one precise question.
- **The module is pasted, not injected.** This will not edit your source.
- **Macro-generated functions are invisible**, because `syn` sees a `macro_rules!` body as
  opaque tokens.

## Two kinds of vacuity, and this is the second one

Vacuity comes in two flavours and they need different tools.

**Preconditions.** An unsatisfiable `assume` means nothing reaches the assertion, so the
property holds over an empty input set. Kani already ships the detector for this:
`kani::cover`. A separate [minimal reproduction](https://github.com/KyleClouthier/kani-vacuity-demo)
shows four of five harness styles reporting `SUCCESSFUL` on knowingly broken code for
exactly this reason.

**Postconditions**, which is what this tool is for. The code runs, every input reaches the
assertion, the proof is sound and the verdict is correct. The clause itself has no content.
**Reachability analysis cannot detect this, because nothing is unreachable.** `kani::cover`
sees a completely healthy harness, because the harness *is* healthy.

## Prior art

Vacuity detection is not new and this does not claim to be. Beer, Ben-David, Eisner and
Rodeh introduced it (CAV 1997); Kupferman and Vardi established that coverage is its dual
(CONCUR 2006); Tomb carried it into deductive verification (2025).

What is here is that mechanised for Rust contracts, where the
[std-contracts project goal](https://rust-lang.github.io/rust-project-goals/2025h1/std-contracts.html)
states safety conditions already live in documentation and is moving them into programmatic
contracts, and describes no mechanism for checking whether a ported contract preserved
anything.

## Licence

MIT OR Apache-2.0.
