-- Extract of GoInLean/Properties/Bits.lean (go-in-lean, 2026-11-01)
theorem Add64_nopre_refuted :
    ¬ ∀ x y carry : uint64,
      ((Add64 x y carry).2.zeroExtend 128 <<< 64) ||| (Add64 x y carry).1.zeroExtend 128
        = x.zeroExtend 128 + y.zeroExtend 128 + carry.zeroExtend 128 := by
  intro h
  have := h 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 2
  revert this
  decide
