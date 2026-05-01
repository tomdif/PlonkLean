import PlonkLean.Circuits.Gadgets

/-! # SHA-256 round structure (TIER 4, scoped, stub)

This file delivers the **structural shape** of one SHA-256 compression-function
round, together with the bitwise primitives (`Ch`, `Maj`, `Σ₀`, `Σ₁`, `σ₀`,
`σ₁`) and the message-schedule expansion.

SHA-256 operates on 32-bit words. We abstract over a `Word` type with a
bundle of bitwise / modular operations (`WordOps`), so this skeleton can
later be instantiated with `Fin (2 ^ 32)`, `BitVec 32`, a vector of `Bool`s,
or even field elements with appropriate constraints.

We are **not** attempting full SHA-256 cryptographic correctness — only
the round's algebraic shape and a few rfl-level structural lemmas.
No sorries.
-/

namespace PlonkLean.Circuits

/-! ## Word operations bundle

The bitwise / modular primitives we need: XOR, AND, NOT, addition mod
`2^32`, right shift by a fixed amount, and rotate-right by a fixed amount. -/

/-- Bundle of word-level operations needed to define one SHA-256 round. -/
structure WordOps (Word : Type*) where
  /-- Bitwise XOR of two words. -/
  xor : Word → Word → Word
  /-- Bitwise AND of two words. -/
  and : Word → Word → Word
  /-- Bitwise NOT of a word. -/
  not : Word → Word
  /-- Addition modulo `2 ^ 32`. -/
  addMod32 : Word → Word → Word
  /-- Logical right shift by `n` bit positions. -/
  shr : Nat → Word → Word
  /-- Rotate right by `n` bit positions (within a 32-bit word). -/
  rotr : Nat → Word → Word

namespace WordOps

variable {Word : Type*}

/-- Iterated XOR over a list, given a `zero` element. -/
def xorList (ops : WordOps Word) (zero : Word) : List Word → Word
  | [] => zero
  | x :: xs => ops.xor x (xorList ops zero xs)

/-- Iterated `addMod32` over a list, given a `zero` element. -/
def addList (ops : WordOps Word) (zero : Word) : List Word → Word
  | [] => zero
  | x :: xs => ops.addMod32 x (addList ops zero xs)

end WordOps

/-! ## SHA-256 bitwise functions

All six are parametric in `WordOps Word`. -/

variable {Word : Type*}

/-- `Ch x y z = (x ∧ y) ⊕ ((¬ x) ∧ z)`. -/
def Ch (ops : WordOps Word) (x y z : Word) : Word :=
  ops.xor (ops.and x y) (ops.and (ops.not x) z)

/-- `Maj x y z = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
def Maj (ops : WordOps Word) (x y z : Word) : Word :=
  ops.xor (ops.and x y) (ops.xor (ops.and x z) (ops.and y z))

/-- `Σ₀ x = ROTR^2 x ⊕ ROTR^13 x ⊕ ROTR^22 x`. -/
def bigSigma0 (ops : WordOps Word) (x : Word) : Word :=
  ops.xor (ops.rotr 2 x) (ops.xor (ops.rotr 13 x) (ops.rotr 22 x))

/-- `Σ₁ x = ROTR^6 x ⊕ ROTR^11 x ⊕ ROTR^25 x`. -/
def bigSigma1 (ops : WordOps Word) (x : Word) : Word :=
  ops.xor (ops.rotr 6 x) (ops.xor (ops.rotr 11 x) (ops.rotr 25 x))

/-- `σ₀ x = ROTR^7 x ⊕ ROTR^18 x ⊕ SHR^3 x`. -/
def smallSigma0 (ops : WordOps Word) (x : Word) : Word :=
  ops.xor (ops.rotr 7 x) (ops.xor (ops.rotr 18 x) (ops.shr 3 x))

/-- `σ₁ x = ROTR^17 x ⊕ ROTR^19 x ⊕ SHR^10 x`. -/
def smallSigma1 (ops : WordOps Word) (x : Word) : Word :=
  ops.xor (ops.rotr 17 x) (ops.xor (ops.rotr 19 x) (ops.shr 10 x))

/-! ## State

The SHA-256 state is eight 32-bit words `(a, b, c, d, e, f, g, h)`. -/

/-- The SHA-256 working state: eight `Word`s indexed by `Fin 8`. -/
def SHA256State (Word : Type*) : Type _ := Fin 8 → Word

namespace SHA256State

variable {Word : Type*}

/-- Read a register at index `i`. -/
@[inline] def get (s : SHA256State Word) (i : Fin 8) : Word := s i

/-- Pointwise update of a register. -/
def update (s : SHA256State Word) (i : Fin 8) (v : Word) : SHA256State Word :=
  fun i' => if i' = i then v else s i'

/-- Build a state from eight explicit values `(a, b, c, d, e, f, g, h)`. -/
def ofTuple (a b c d e f g h : Word) : SHA256State Word :=
  fun i => match i with
    | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d
    | ⟨4, _⟩ => e | ⟨5, _⟩ => f | ⟨6, _⟩ => g | ⟨7, _⟩ => h
    | ⟨n + 8, h'⟩ => by exact absurd h' (by omega)

end SHA256State

/-! ## One compression round

Given the current state `(a, b, c, d, e, f, g, h)`, the round constant
`K_i`, and the schedule word `W_i`, the new state is

```
T1 = h + Σ₁(e) + Ch(e, f, g) + K_i + W_i
T2 = Σ₀(a) + Maj(a, b, c)
new = (T1 + T2, a, b, c, d + T1, e, f, g)
```

All additions are mod `2^32`. -/

/-- One SHA-256 compression-function round. -/
def sha256Round (ops : WordOps Word) (K W : Word) (s : SHA256State Word) :
    SHA256State Word :=
  let a := s 0
  let b := s 1
  let c := s 2
  let d := s 3
  let e := s 4
  let f := s 5
  let g := s 6
  let h := s 7
  let T1 := ops.addMod32 h
              (ops.addMod32 (bigSigma1 ops e)
                (ops.addMod32 (Ch ops e f g)
                  (ops.addMod32 K W)))
  let T2 := ops.addMod32 (bigSigma0 ops a) (Maj ops a b c)
  SHA256State.ofTuple
    (ops.addMod32 T1 T2)         -- new a
    a                            -- new b
    b                            -- new c
    c                            -- new d
    (ops.addMod32 d T1)          -- new e
    e                            -- new f
    f                            -- new g
    g                            -- new h

/-! ## Message schedule

The 512-bit input block is parsed into 16 words `M₀, …, M₁₅`. The schedule
`W : Fin 64 → Word` is then defined by

```
W_t = M_t                                                if 0 ≤ t < 16,
W_t = σ₁(W_{t-2}) + σ₀(W_{t-15}) + W_{t-7} + W_{t-16}    if 16 ≤ t < 64.
```

We model the 16-word block by `M : Fin 16 → Word` and compute the schedule
as a function `Fin 64 → Word` via `Nat.rec`-style recursion. -/

/-- One step of the schedule recurrence, taking the four prior words
`W_{t-2}`, `W_{t-7}`, `W_{t-15}`, `W_{t-16}` directly:

`σ₁(W_{t-2}) + σ₀(W_{t-15}) + W_{t-7} + W_{t-16}`. -/
def scheduleStep (ops : WordOps Word) (wm2 wm7 wm15 wm16 : Word) : Word :=
  ops.addMod32 (smallSigma1 ops wm2)
    (ops.addMod32 (smallSigma0 ops wm15)
      (ops.addMod32 wm7 wm16))

/-- Read the `i`-th element of a list, returning `zero` if out of range. -/
def nthOr (zero : Word) : List Word → Nat → Word
  | [], _ => zero
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nthOr zero xs n

/-- Auxiliary: extend a list of already-computed schedule words `W₀..W_{t-1}`
(stored in order) by `n` more steps. The list is the full prefix; new words
are appended on the right. -/
def extendSchedule (ops : WordOps Word) (zero : Word) :
    Nat → List Word → List Word
  | 0,     ws => ws
  | n + 1, ws =>
      let t := ws.length
      let next :=
        scheduleStep ops
          (nthOr zero ws (t - 2))
          (nthOr zero ws (t - 7))
          (nthOr zero ws (t - 15))
          (nthOr zero ws (t - 16))
      extendSchedule ops zero n (ws ++ [next])

/-- Build the full 64-word schedule as a `List Word` of length 64.
The first 16 entries are `M₀..M₁₅`; entries 16..63 are computed by the
recurrence. -/
def sha256ScheduleList (ops : WordOps Word) (zero : Word)
    (M : Fin 16 → Word) : List Word :=
  let initial : List Word := (List.finRange 16).map M
  extendSchedule ops zero 48 initial

/-- The 64-word SHA-256 message schedule, packaged as `Fin 64 → Word`. -/
def sha256Schedule (ops : WordOps Word) (zero : Word)
    (M : Fin 16 → Word) : Fin 64 → Word :=
  fun t => nthOr zero (sha256ScheduleList ops zero M) t.val

/-! ## Sanity / structural lemmas

These are *trivial* shape-level rewrites — we are not proving any
cryptographic content here. -/

variable (ops : WordOps Word)

/-- `Ch` unfolds to its definition. -/
theorem Ch_def (x y z : Word) :
    Ch ops x y z = ops.xor (ops.and x y) (ops.and (ops.not x) z) := rfl

/-- `Maj` unfolds to its definition. -/
theorem Maj_def (x y z : Word) :
    Maj ops x y z
      = ops.xor (ops.and x y) (ops.xor (ops.and x z) (ops.and y z)) := rfl

/-- `Σ₀` unfolds to its definition. -/
theorem bigSigma0_def (x : Word) :
    bigSigma0 ops x
      = ops.xor (ops.rotr 2 x) (ops.xor (ops.rotr 13 x) (ops.rotr 22 x)) := rfl

/-- `Σ₁` unfolds to its definition. -/
theorem bigSigma1_def (x : Word) :
    bigSigma1 ops x
      = ops.xor (ops.rotr 6 x) (ops.xor (ops.rotr 11 x) (ops.rotr 25 x)) := rfl

/-- `σ₀` unfolds to its definition. -/
theorem smallSigma0_def (x : Word) :
    smallSigma0 ops x
      = ops.xor (ops.rotr 7 x) (ops.xor (ops.rotr 18 x) (ops.shr 3 x)) := rfl

/-- `σ₁` unfolds to its definition. -/
theorem smallSigma1_def (x : Word) :
    smallSigma1 ops x
      = ops.xor (ops.rotr 17 x) (ops.xor (ops.rotr 19 x) (ops.shr 10 x)) := rfl

/-- `sha256Round` unfolds to the explicit `(T1 + T2, a, b, c, d + T1, e, f, g)`
state, modulo `let`-zeta. We expose the post-`let` body. -/
theorem sha256Round_def (K W : Word) (s : SHA256State Word) :
    sha256Round ops K W s
      = (let a := s 0
         let b := s 1
         let c := s 2
         let d := s 3
         let e := s 4
         let f := s 5
         let g := s 6
         let h := s 7
         let T1 := ops.addMod32 h
                     (ops.addMod32 (bigSigma1 ops e)
                       (ops.addMod32 (Ch ops e f g)
                         (ops.addMod32 K W)))
         let T2 := ops.addMod32 (bigSigma0 ops a) (Maj ops a b c)
         SHA256State.ofTuple
           (ops.addMod32 T1 T2) a b c
           (ops.addMod32 d T1) e f g) := rfl

/-- The schedule recurrence step unfolds to its definition. -/
theorem scheduleStep_def (wm2 wm7 wm15 wm16 : Word) :
    scheduleStep ops wm2 wm7 wm15 wm16
      = ops.addMod32 (smallSigma1 ops wm2)
          (ops.addMod32 (smallSigma0 ops wm15)
            (ops.addMod32 wm7 wm16)) := rfl

/-- `sha256Schedule` agrees with the underlying list lookup. -/
theorem sha256Schedule_apply (zero : Word) (M : Fin 16 → Word) (t : Fin 64) :
    sha256Schedule ops zero M t
      = nthOr zero (sha256ScheduleList ops zero M) t.val := rfl

/-- `SHA256State.ofTuple` reads back the 0-th component as `a`. -/
theorem ofTuple_zero (a b c d e f g h : Word) :
    (SHA256State.ofTuple a b c d e f g h) 0 = a := rfl

/-- `SHA256State.ofTuple` reads back the 4-th component as `e`. -/
theorem ofTuple_four (a b c d e f g h : Word) :
    (SHA256State.ofTuple a b c d e f g h) 4 = e := rfl

end PlonkLean.Circuits
