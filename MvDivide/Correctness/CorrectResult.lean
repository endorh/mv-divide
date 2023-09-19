import Mathlib.Logic.Basic
import Mathlib.Init.ZeroOne
import Mathlib.Init.Algebra.Classes

/-- Result of an algorithm paired with a proof that it is correct.

Conceptually equivalent to `Subtype`, to/from which can be cast.
Likewise, a `CorrectResult α p` can be coerced to `α`.

Supports *nice* syntax and the `alg` attribute to concisely declare
self-correctness-proving algorithms:
```lean4
@[alg simp]
def sum_alg (a b : ℕ) : ℕ
such_that it - b = a :=
  a + b
correct_by
  simp_arith
```

This example translates to:
```lean4
def sum_alg (a b : ℕ) : CorrectResult ℕ (λit => it - b = a) :=
  ⟨a + b, by simp_arith⟩

def sum (a b : ℕ) : ℕ :=
  (sum_alg a b).res
@[simp]
lemma sum_spec (a b : ℕ) : sum a b - b = a :=
  (sum_alg a b).correctness
```

Thanks to the compiler's propositional erasure, the actual implementation of
both `sum` and `sum_alg` in the above example are streamlined during
compilation, skipping any operations related to the proof, producing an
algorithm no less efficient than we could have obtained by manually declaring
`sum` and having to painfully introspect it within `sum_spec` to separately
prove its correctness.
LLVM compilation should also likely inline the call to `sum_alg` from `sum`.

The benefits of this approach are more notable in algorithms that have
multiple cases, since we *match the proof on each case* at the same
time we define the cases (since `correct_by` must be applied on
each *return point*).

In addition, the `alg` attribute allows users of `sum` to *simply use* our
algorithm, without having to know about `CorrectResult` at all, while also
having `sum_spec` as a lemma available to the simplifier, with no more
than a single declaration from our part.
-/
@[ext]
structure CorrectResult (α : Type _) (p : α → Prop) where
  res : α
  correctness : p res
deriving Repr

namespace CorrectResult

-- We can't use `Coe`, since our input type is not concrete (`p` is a free parameter).
-- The coercion mechanism searches for coercion instances from the expected type
-- backwards, so the left parameter of `Coe` is declared as `semiOutputParam` to
-- enforce that it doesn't contain free metavariables that could increase the amount
-- of instances to search exponentially.

-- However, in some cases, such as this, we may want to define a *forgetful* coercion
-- that doesn't depend on some of the parameters of the input type.
-- This is precisely what `CoeHead` represents. The coercion mechanism can also try
-- to coerce forward using head coercions and the inferred type of the mistyped
-- expression. Naturally, for `CoeHead`, the `semiOutputParam` is the right parameter.

-- Another class, `CoeTail` also exists, but has a different purpose, preventing
-- unwanted coercion chains, for example when a coercion is not *natural* in some way,
-- and only makes sense for a specific type, or when a coercion could create coercion
-- loops, such as typed alias coercions (e.g., `TSyntax`)
instance coeResult : CoeHead (CorrectResult α p) α where
  coe a := a.res

-- Casts to/from `Subtype p`
instance coeSubtype : Coe (CorrectResult α p) (Subtype p) where
  coe a := ⟨a.res, a.correctness⟩
instance coeFromSubtype (p : α → Prop) : Coe (Subtype p) (CorrectResult α p) where
  coe a := ⟨a.val, a.property⟩

section Notation
open Lean Lean.Syntax

/-- Use `such_that` to specify a correctness property verified by the result
(`it`) of an algorithm (see `CorrectResult`).

To use pattern matching or an hygienic name instead of `it` write
`such_that x => ...`, where `x` can be a pattern.

```lean4
def sum (a b : ℕ) : ℕ
such_that it - b = a :=
  a + b
correct_by
  simp_arith
```-/
syntax:min (name := such_that) term " such_that " term : term

/-- Use `such_that` to specify a correctness property verified by the result
of an algorithm (see `CorrectResult`).

If you don't need pattern matching, consider not specifying a binder name
and using `it` as the implicit default (`such_that it = ...`).

```lean4
def sum (a b : ℕ) : ℕ
such_that it - b = a :=
  a + b
correct_by
  simp_arith
```-/
syntax:min (name := hygienic_such_that) term " such_that " term " => " term : term

/-- Use `correct_by` to provide a correctness proof for an algorithm
(see `CorrectResult`).
```lean4
def sum (a b : ℕ) : ℕ
such_that it - b = a :=
  a + b
correct_by
  simp_arith
```-/
syntax:min (name := correct_by) term " correct_by " tacticSeq : term

-- We also define `it` as a *keyword*, which is directly translated to the
-- identifier with the same name, simply to highlight it in a different
-- color, as well as provide some clarification through the documentation
-- popup, similar to `this`
/-- Implicit name for single-parameter lambdas in some contexts (unhygienic). -/
syntax (name := unhygienic_it_ident) "it" : term

macro_rules
| `(it) => `($(Lean.mkIdent `it))
| `($t:term such_that $c:term) => `(CorrectResult $t λ$(mkIdent `it) => $c)
| `($t:term such_that $pat:term => $c:term) => `(CorrectResult $t λ$pat => $c)

-- We use `withRef` to report problems (and other metadata) from the proof at
-- the `correct_by` keyword, instead of the whole macro, which could result in
-- an error being reported confusingly at `$v` (which has nothing to do with the
-- proof) if `correct_by` were on a new line (since error highlight ranges are
-- trimmed to the first line of the erroring syntax node to prevent
-- red squiggly hell)

-- This is similar to how problems in a multiline `by` proof are reported at
-- the `by` keyword (albeit in that case it's just a natural consequence of the
-- error being trimmed to the first line, since the `by` keyword is conveniently
-- the first word of the syntax node, and everything lines up nicely)

-- The `correct_by%$c` syntax extracts the `correct_by` node with the name `c`.
-- For some reason, neither of the following abbreviations seem to work here,
-- so we must use `withRef` manually:
-- | `($v:term correct_by%$c $s:tacticSeq) => `(CorrectResult.mk $v (by%$c $s))
-- | `($v:term correct_by%$c $s:tacticSeq) => `(CorrectResult.mk $v (by $s)%$c)
-- The `do` block is necessary to conveniently lift the result of `withRef`
-- from the `MacroM` monad inside the expression antiquotation
| `($v:term correct_by%$c $s:tacticSeq) => do
  `(CorrectResult.mk $v $(←withRef c `(by $s)))

-- #check_failure λa b : ℕ => (
--     a + b
--   correct_by -- 'unsolved goals' should be reported here, not at `a + b`
--     try trivial
-- : ℕ such_that it - b = a)

end Notation
end CorrectResult