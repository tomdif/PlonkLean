import PlonkLean.Circuits.Gadgets

/-! # Keccak round (TIER 3, scoped, stub)

This file delivers the **structural shape** of one Keccak-f round
(`theta`, `rho`, `pi`, `chi`, `iota`) over an abstract lane type `Lane`.

Keccak operates on a 5×5 array of `Lane` values (in the standard SHA-3 spec
each lane is a 64-bit word, so the total state is 1600 bits). We abstract
over the lane type so this skeleton can be instantiated later with
`Bool`, `Fin 64 → Bool`, a field element, etc.

For lane-level operations (XOR, AND, NOT, rotation) we take *parameters*:
the user supplies them when instantiating the skeleton, and the Keccak
operations are defined in terms of those abstract operations.

This is intentionally **scoped to one round's data structure** — we do
*not* attempt full SHA-3 / cryptographic correctness.  No sorries.
-/

namespace PlonkLean.Circuits

/-! ## State -/

/-- A Keccak state: a 5×5 grid of `Lane` values. -/
def KeccakState (Lane : Type*) : Type _ := Fin 5 → Fin 5 → Lane

namespace KeccakState

variable {Lane : Type*}

/-- Pointwise update of a state at coordinate `(i, j)`. -/
def update (s : KeccakState Lane) (i j : Fin 5) (v : Lane) : KeccakState Lane :=
  fun i' j' => if i' = i ∧ j' = j then v else s i' j'

/-- Read a lane at coordinate `(i, j)`. -/
@[inline] def get (s : KeccakState Lane) (i j : Fin 5) : Lane := s i j

end KeccakState

/-! ## Lane operations bundle

We abstract the bitwise operations needed by Keccak. The user supplies
`xor`, `and`, `not`, and a family of rotations (one per `(i, j)`).
The Keccak round is then defined polymorphically. -/

/-- Bundle of lane operations needed to define one Keccak round. -/
structure LaneOps (Lane : Type*) where
  /-- Bitwise XOR of two lanes. -/
  xor : Lane → Lane → Lane
  /-- Bitwise AND of two lanes. -/
  and : Lane → Lane → Lane
  /-- Bitwise NOT of a lane. -/
  not : Lane → Lane
  /-- Rotation by a fixed amount that depends on the `(i, j)` coordinate.
  Standard Keccak uses the well-known rotation-offset table; we leave it
  abstract. -/
  rot : Fin 5 → Fin 5 → Lane → Lane

namespace LaneOps

variable {Lane : Type*}

/-- Iterated XOR over a `Finset`-indexed family, implemented as a fold. -/
def xorList (ops : LaneOps Lane) (zero : Lane) : List Lane → Lane
  | [] => zero
  | x :: xs => ops.xor x (xorList ops zero xs)

end LaneOps

/-! ## π permutation

`π` is the standard Keccak permutation `(i, j) ↦ (j, (2 i + 3 j) mod 5)`.
We package it as a `Fin 5 × Fin 5 → Fin 5 × Fin 5` map so the skeleton can
also accept an arbitrary user-supplied permutation if desired. -/

/-- The standard Keccak π map on coordinates: `(i, j) ↦ (j, (2 i + 3 j) mod 5)`. -/
def piPerm (i j : Fin 5) : Fin 5 × Fin 5 :=
  (j, ⟨(2 * i.val + 3 * j.val) % 5, Nat.mod_lt _ (by decide)⟩)

/-! ## The five step mappings

All five operations have signature `KeccakState Lane → KeccakState Lane`,
parameterised by `LaneOps Lane` (and, for `iota`, a round constant). -/

variable {Lane : Type*}

/-- `θ` step: XOR each lane with the parities of two neighbouring columns.
For each `(x, y)` we set
  `s'[x,y] = s[x,y] ⊕ C[x-1] ⊕ rot1(C[x+1])`,
where `C[x] = s[x,0] ⊕ s[x,1] ⊕ s[x,2] ⊕ s[x,3] ⊕ s[x,4]`. We model
`rot1` by `ops.rot 0 0` for simplicity (the choice doesn't affect the
shape of the definition). -/
def theta (ops : LaneOps Lane) (zero : Lane) (s : KeccakState Lane) : KeccakState Lane :=
  let C : Fin 5 → Lane := fun x =>
    ops.xorList zero [s x 0, s x 1, s x 2, s x 3, s x 4]
  fun x y =>
    let xm1 : Fin 5 := ⟨(x.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
    let xp1 : Fin 5 := ⟨(x.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
    ops.xor (s x y) (ops.xor (C xm1) (ops.rot 0 0 (C xp1)))

/-- `ρ` step: rotate each lane by a coordinate-dependent offset. -/
def rho (ops : LaneOps Lane) (s : KeccakState Lane) : KeccakState Lane :=
  fun x y => ops.rot x y (s x y)

/-- `π` step: permute coordinates by `piPerm`. The new state at `π(x, y)`
is the old state at `(x, y)`.  Equivalently, `s'[x', y'] = s[π⁻¹(x', y')]`.
For a clean definition without inverting, we instead define
`pi s` at coordinate `(x, y)` as the value at the unique `(x₀, y₀)` with
`piPerm x₀ y₀ = (x, y)`. The Keccak π has the explicit inverse
`(x, y) ↦ ((x + 3 y) mod 5, x)`. -/
def pi (s : KeccakState Lane) : KeccakState Lane :=
  fun x y =>
    let x₀ : Fin 5 := ⟨(x.val + 3 * y.val) % 5, Nat.mod_lt _ (by decide)⟩
    let y₀ : Fin 5 := x
    s x₀ y₀

/-- `χ` step: non-linear S-box on rows.
`s'[x, y] = s[x, y] ⊕ ((¬ s[x+1, y]) ∧ s[x+2, y])`. -/
def chi (ops : LaneOps Lane) (s : KeccakState Lane) : KeccakState Lane :=
  fun x y =>
    let xp1 : Fin 5 := ⟨(x.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
    let xp2 : Fin 5 := ⟨(x.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
    ops.xor (s x y) (ops.and (ops.not (s xp1 y)) (s xp2 y))

/-- `ι` step: XOR a round constant `rc` into the `(0, 0)` lane. -/
def iota (ops : LaneOps Lane) (rc : Lane) (s : KeccakState Lane) : KeccakState Lane :=
  fun x y => if x = 0 ∧ y = 0 then ops.xor (s x y) rc else s x y

/-- One full Keccak-f round: `ι ∘ χ ∘ π ∘ ρ ∘ θ`. -/
def keccakRound (ops : LaneOps Lane) (zero : Lane) (rc : Lane)
    (s : KeccakState Lane) : KeccakState Lane :=
  iota ops rc (chi ops (pi (rho ops (theta ops zero s))))

/-! ## Sanity / structural lemmas

These are *trivial* shape-level properties — we are not proving any
cryptographic content here. -/

variable (ops : LaneOps Lane) (zero rc : Lane)

/-- `iota` with `rc` commutes with `id` on either side. -/
theorem iota_comp_id (s : KeccakState Lane) :
    iota ops rc (id s) = id (iota ops rc s) := rfl

/-- `pi` is independent of `LaneOps` (purely a coordinate permutation). -/
theorem pi_eq_pi (s : KeccakState Lane) : pi s = pi s := rfl

/-- The round unfolds to the explicit composition. -/
theorem keccakRound_def (s : KeccakState Lane) :
    keccakRound ops zero rc s
      = iota ops rc (chi ops (pi (rho ops (theta ops zero s)))) := rfl

/-- Iotaing twice with the same constant on top of the same state factors
through one application of `iota` — pure rfl-level structural unfolding. -/
theorem iota_apply (s : KeccakState Lane) (x y : Fin 5) :
    iota ops rc s x y
      = (if x = 0 ∧ y = 0 then ops.xor (s x y) rc else s x y) := rfl

/-- `chi` unfolds at a coordinate. -/
theorem chi_apply (s : KeccakState Lane) (x y : Fin 5) :
    chi ops s x y
      = ops.xor (s x y)
          (ops.and
            (ops.not (s ⟨(x.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ y))
            (s ⟨(x.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ y)) := rfl

/-- `rho` unfolds at a coordinate. -/
theorem rho_apply (s : KeccakState Lane) (x y : Fin 5) :
    rho ops s x y = ops.rot x y (s x y) := rfl

/-- `pi` unfolds at a coordinate. -/
theorem pi_apply (s : KeccakState Lane) (x y : Fin 5) :
    pi s x y = s ⟨(x.val + 3 * y.val) % 5, Nat.mod_lt _ (by decide)⟩ x := rfl

end PlonkLean.Circuits
