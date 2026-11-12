import LemLib
/-
  Utility functions for Cerberus Lean port.
  Corresponds to various OCaml modules.
  Leaf module — no imports from generated code.
-/

namespace CerbUtils

/-! ## Timing
    Corresponds to: Cerb_debug.begin_timing/end_timing in cerb_debug.ml
    (OCaml records wall-clock time to cerb.prof).
    VALUE IDENTITIES (seam-hygiene H3, 2026-09-19, docs/2026-09-18_seam-
    hygiene-record.md §5; were `opaque … implemented_by` no-op impls beside an
    intentionally unread `IO.Ref`, arc-14 S1 F6): profiling is not ported (it
    is not observable on any differential path), so both are plain `def`s
    returning `()` — kernel-transparent, nothing hidden, no boundary row. -/

def begin_timing (_ : String) : Unit := ()

def end_timing (_ : Unit) : Unit := ()

/-! ## Driver memory-event trace
    Corresponds to: driver.lem `record_trace_event` (`ev :: tr` in OCaml).
    VALUE IDENTITY on the list: the OCaml trace is read only by `--trace`
    (driver_ocaml.ml:290-301) and the web UI; this port has no `--trace`
    and nothing reads `driver_state.trace` (CerbMem.prefixOfPointer note).
    Keeping the events retained every load/store/kill with its values for
    the whole run. Restore the cons here if a `--trace` printer is ported. -/
def record_trace_event {α : Type} (_ : α) (tr : List α) : List α := tr

/-! ## Logging
    Corresponds to: Cerb_logging.log_standard in cerb_logging.ml — the OCaml
    side logs the ISO citation and returns the value unchanged. VALUE IDENTITY
    (seam-hygiene H3): the former impl pushed the string onto an `IO.Ref`
    that nothing ever read (grep over the tree, record §5), so `STD_ s x = x`
    as a plain `def`; the `[Inhabited α]` binder went with the impl (generated
    call sites pass the two explicit arguments only). -/

def STD_ {α : Type} (_ : String) (x : α) : α := x

/-! ## List utilities
    Corresponds to: OCaml List.remove_assoc -/

def list_remove_assoc {α β : Type} [BEq α] (key : α) : List (α × β) → List (α × β)
  | [] => []
  | (k, v) :: rest => if k == key then rest else (k, v) :: list_remove_assoc key rest

/-! ## Random bounded integer
    Corresponds to: Cerb_any.bounded_integer in cerb_any.ml, called only from
    the `any_bounded_int` arm of `Core_run.core_thread_step2`
    (core_run.lem:1076-1086), a stepper the driver never runs. The live
    stepper, `Core_reduction.core_step2`, fails `any_bounded_int` with
    "TODO Core_reduction ==> any_bounded_int()" in BOTH engines
    (core_reduction.lem:1012-1013; served-surface audit P3-1, measured:
    oracle rc 125, Lean PANIC) — a mirrored failure. This seam used to
    return `lo` where the oracle draws from a time-seeded PRNG
    (util/cerb_any.ml:1-9); it now fails loudly so it can never become a
    silent answer if the stepper changes (zero-discrepancy Z2-U-02,
    reclassified 2026-09-28). -/
def bounded_integer (_lo _hi : Int) : Int :=
  failwithI "CerbUtils.bounded_integer: any_bounded_int is not modelled (the oracle draws from a time-seeded PRNG; its live stepper fails this builtin, core_reduction.lem:1012-1013)"

/-! ## Character encoding
    Corresponds to: Decode.encode_character_constant in decode.ml:223-225:
    `Char.chr (Z.to_int n land 0xff)` — the LOW 8 BITS of the two's
    complement value, i.e. the euclidean n mod 256 (so e.g. -1 → 255,
    200 → 200; the previous `% 128` clamp was survey finding 28). Lean's
    Int.emod is euclidean (non-negative for a positive modulus), and
    codepoints 0-255 are all valid Chars. -/

def encode_character_constant (n : Int) : Char :=
  Char.ofNat (Int.emod n 256).toNat

/-! ## List utilities -/

/-- OCaml List.init: create list of length n using function f.
    Corresponds to: List.init in OCaml stdlib -/
def list_init {α : Type} (n : Nat) (f : Nat → α) : List α :=
  (List.range n).map f

/-- Check if integer is a power of two.
    Corresponds to: Cerb_util.is_power_of_two -/
def is_power_of_two (n : Int) : Bool :=
  n > 0 && (n.toNat &&& (n.toNat - 1)) == 0

/-! ## GCC builtins — ocaml_frontend/ocaml_gcc_builtins.ml, mirrored
    per-line (arc-14 S1 F2, sem:G4: the previous versions clamped via
    Int.toNat — so ffs(-1) = 0 where the oracle's Z semantics give 1 —
    and silently masked/wrapped where the oracle asserts range). -/

/-- Number of trailing zero bits of |n|, n ≠ 0 — Z.trailing_zeros (GMP
    mpz_scan1) semantics: the two's-complement view and |n| agree on
    trailing zeros (-n = ~n + 1 preserves them), so natAbs is exact for
    negatives. Computed arithmetically: v &&& (v ^^^ (v-1)) isolates the
    lowest set bit 2^k; log2 recovers k. -/
private def trailingZerosZ (n : Int) : Nat :=
  let v := n.natAbs
  Nat.log2 (v &&& (v ^^^ (v - 1)))

/-- generic_ffs — ocaml_gcc_builtins.ml:47-51:
    `if n = 0 then n else Z.of_int (1 + Z.trailing_zeros n)`.
    Arbitrary-precision Z: a negative (signed int) argument is
    well-defined — ffs(-1) = 1, ffs(INT_MIN) = 32. -/
def gcc_builtin_generic_ffs (n : Int) : Int :=
  if n == 0 then 0
  else Int.ofNat (1 + trailingZerosZ n)

/-- ctz — ocaml_gcc_builtins.ml:3-11: `assert (not (equal n zero))`
    (ctz(0) is undefined per the GCC docs — the oracle assert-crashes;
    mirrored as a panic), then the trailing-zero count of the int64
    two's-complement pattern (upstream's shift-left loop computes
    exactly trailing_zeros). -/
def gcc_builtin_ctz (n : Int) : Int :=
  if n == 0 then
    failwithI "Ocaml_gcc_builtins.ctz: zero argument (ocaml_gcc_builtins.ml:5 assert)"
  else Int.ofNat (trailingZerosZ n)

/-- bswap16 — ocaml_gcc_builtins.ml:13-18:
    `assert (equal zero (logand 0xffffffffffff0000L n))` — any value
    outside [0, 0xFFFF] (negatives included: sign-extension sets high
    bits) assert-crashes; mirrored as a panic (was: silent % 0x10000
    wrap). Swap per :16-17. -/
def gcc_builtin_bswap16 (n : Int) : Int :=
  if n < 0 || n > 0xFFFF then
    failwithI "Ocaml_gcc_builtins.bswap16: out of range (ocaml_gcc_builtins.ml:15 assert)"
  else
    let v := n.toNat
    Int.ofNat (((v &&& 0xFF) <<< 8) ||| ((v >>> 8) &&& 0xFF))

/-- bswap32 — ocaml_gcc_builtins.ml:20-27: same assert shape for
    [0, 0xFFFFFFFF]; swap per :24-26. -/
def gcc_builtin_bswap32 (n : Int) : Int :=
  if n < 0 || n > 0xFFFFFFFF then
    failwithI "Ocaml_gcc_builtins.bswap32: out of range (ocaml_gcc_builtins.ml:22 assert)"
  else
    let v := n.toNat
    let b0 := v &&& 0xFF
    let b1 := (v >>> 8) &&& 0xFF
    let b2 := (v >>> 16) &&& 0xFF
    let b3 := (v >>> 24) &&& 0xFF
    Int.ofNat ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3)

/-- bswap64 — ocaml_gcc_builtins.ml:29-40: no range assert, but
    `Z.to_int64` RAISES Overflow outside the int64 range (mirrored as a
    panic), the swap runs on the 64-bit two's-complement pattern, and
    the result is re-read SIGNED (`Z.of_int64`) — a swapped value with
    bit 63 set comes back negative. All three mirrored (was: toNat
    clamp + always-unsigned result). -/
def gcc_builtin_bswap64 (n : Int) : Int :=
  if n < -(2 ^ 63) || n ≥ 2 ^ 63 then
    failwithI "Ocaml_gcc_builtins.bswap64: Z.to_int64 overflow (ocaml_gcc_builtins.ml:30)"
  else
    let v := (Int.emod n (2 ^ 64)).toNat  -- the int64 bit pattern (euclidean mod)
    let b0 := v &&& 0xFF
    let b1 := (v >>> 8) &&& 0xFF
    let b2 := (v >>> 16) &&& 0xFF
    let b3 := (v >>> 24) &&& 0xFF
    let b4 := (v >>> 32) &&& 0xFF
    let b5 := (v >>> 40) &&& 0xFF
    let b6 := (v >>> 48) &&& 0xFF
    let b7 := (v >>> 56) &&& 0xFF
    let u := (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
             (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7
    -- Z.of_int64: signed reinterpretation of the swapped pattern
    if u ≥ 2 ^ 63 then Int.ofNat u - 2 ^ 64 else Int.ofNat u

end CerbUtils
