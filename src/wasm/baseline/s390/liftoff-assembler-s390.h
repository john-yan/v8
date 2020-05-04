// Copyright 2017 the V8 project authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#ifndef V8_WASM_BASELINE_S390_LIFTOFF_ASSEMBLER_S390_H_
#define V8_WASM_BASELINE_S390_LIFTOFF_ASSEMBLER_S390_H_

#include "src/wasm/baseline/liftoff-assembler.h"


namespace v8 {
namespace internal {
namespace wasm {

namespace liftoff {

//  half
//  slot        Frame
//  -----+--------------------+---------------------------
//  n+3  |   parameter n      |
//  ...  |       ...          |
//   4   |   parameter 1      | or parameter 2
//   3   |   parameter 0      | or parameter 1
//   2   |  (result address)  | or parameter 0
//  -----+--------------------+---------------------------
//   1   | return addr (lr)   |
//   0   | previous frame (fp)|
//  -----+--------------------+  <-- frame ptr (fp)
//  -1   | 0xa: WASM          |
//  -2   |     instance       |
//  -----+--------------------+---------------------------
//  -3   |    slot 0 (high)   |   ^
//  -4   |    slot 0 (low)    |   |
//  -5   |    slot 1 (high)   | Frame slots
//  -6   |    slot 1 (low)    |   |
//       |                    |   v
//  -----+--------------------+  <-- stack ptr (sp)
//
constexpr int32_t kInstanceOffset = 2 * kSystemPointerSize;

inline MemOperand GetHalfStackSlot(int offset, RegPairHalf half) {
  int32_t half_offset =
      half == kLowWord ? 0 : LiftoffAssembler::kStackSlotSize / 2;
  return MemOperand(fp, -offset + half_offset);
}

inline MemOperand GetStackSlot(uint32_t offset) {
  return MemOperand(fp, -offset);
}

inline MemOperand GetInstanceOperand() { return GetStackSlot(kInstanceOffset); }

inline MemOperand GetMemOp(LiftoffAssembler* assm,
                           UseScratchRegisterScope* temps, Register addr,
                           Register offset, int32_t offset_imm) {
  // Wasm memory is limited to a size <4GB.
  DCHECK(is_uint32(offset_imm));
  if (offset != no_reg) {
    assm->iihf(offset, Operand(0));
    if (offset_imm == 0) return MemOperand(addr, offset);
    Register tmp = temps->Acquire();
    assm->iihf(tmp, Operand(0));
    assm->AddP(tmp, offset, Operand(offset_imm));
    return MemOperand(addr, tmp);
  }
  return MemOperand(addr, offset_imm);
}

inline Condition LiftoffCondToCond(Condition cond) {
  switch (cond) {
    case kSignedLessThan:
      return kUnsignedLessThan;
    case kSignedLessEqual:
      return kUnsignedLessEqual;
    case kSignedGreaterThan:
      return kUnsignedGreaterThan;
    case kSignedGreaterEqual:
      return kUnsignedGreaterEqual;
    case kEqual:
    case kUnequal:
    case kUnsignedLessThan:
    case kUnsignedLessEqual:
    case kUnsignedGreaterThan:
    case kUnsignedGreaterEqual:
      return cond;
    default:
      UNREACHABLE();
  }
}

inline void FloatMax(LiftoffAssembler* assm, DoubleRegister result_reg,
                     DoubleRegister left_reg, DoubleRegister right_reg) {
  Label check_nan_left, check_zero, return_left, return_right, done;
  assm->cebr(left_reg, right_reg);
  assm->bunordered(&check_nan_left, Label::kNear);
  assm->beq(&check_zero);
  assm->bge(&return_left, Label::kNear);
  assm->b(&return_right, Label::kNear);

  assm->bind(&check_zero);
  assm->lzdr(kDoubleRegZero);
  assm->cebr(left_reg, kDoubleRegZero);
  /* left == right != 0. */
  assm->bne(&return_left, Label::kNear);
  /* At this point, both left and right are either 0 or -0. */
  /* N.B. The following works because +0 + -0 == +0 */
  /* For max we want logical-and of sign bit: (L + R) */
  assm->ldr(result_reg, left_reg);
  assm->aebr(result_reg, right_reg);
  assm->b(&done, Label::kNear);

  assm->bind(&check_nan_left);
  assm->cebr(left_reg, left_reg);
  // left == NaN.
  assm->bunordered(&return_left, Label::kNear);

  assm->bind(&return_right);
  if (right_reg != result_reg) {
    assm->ldr(result_reg, right_reg);
  }
  assm->b(&done, Label::kNear);

  assm->bind(&return_left);
  if (left_reg != result_reg) {
    assm->ldr(result_reg, left_reg);
  }
  assm->bind(&done);
}

inline void FloatMin(LiftoffAssembler* assm, DoubleRegister result_reg,
                     DoubleRegister left_reg, DoubleRegister right_reg) {
  Label check_nan_left, check_zero, return_left, return_right, done;
  assm->cebr(left_reg, right_reg);
  assm->bunordered(&check_nan_left, Label::kNear);
  assm->beq(&check_zero);
  assm->ble(&return_left, Label::kNear);
  assm->b(&return_right, Label::kNear);

  assm->bind(&check_zero);
  assm->lzdr(kDoubleRegZero);
  assm->cebr(left_reg, kDoubleRegZero);
  // left == right != 0.
  assm->bne(&return_left, Label::kNear);
  // At this point, both left and right are either 0 or -0. */
  // N.B. The following works because +0 + -0 == +0 */
  // For min we want logical-or of sign bit: -(-L + -R) */
  assm->lcebr(left_reg, left_reg);
  assm->ldr(result_reg, left_reg);
  if (left_reg == right_reg) {
    assm->aebr(result_reg, right_reg);
  } else {
    assm->sebr(result_reg, right_reg);
  }
  assm->lcebr(result_reg, result_reg);
  assm->b(&done, Label::kNear);

  assm->bind(&check_nan_left);
  assm->cebr(left_reg, left_reg);
  /* left == NaN. */
  assm->bunordered(&return_left, Label::kNear);

  assm->bind(&return_right);
  if (right_reg != result_reg) {
    assm->ldr(result_reg, right_reg);
  }
  assm->b(&done, Label::kNear);

  assm->bind(&return_left);
  if (left_reg != result_reg) {
    assm->ldr(result_reg, left_reg);
  }
  assm->bind(&done);
}

inline void DoubleMax(LiftoffAssembler* assm, DoubleRegister result_reg,
                      DoubleRegister left_reg, DoubleRegister right_reg) {
  Label check_nan_left, check_zero, return_left, return_right, done;
  assm->cdbr(left_reg, right_reg);
  assm->bunordered(&check_nan_left, Label::kNear);
  assm->beq(&check_zero);
  assm->bge(&return_left, Label::kNear);
  assm->b(&return_right, Label::kNear);

  assm->bind(&check_zero);
  assm->lzdr(kDoubleRegZero);
  assm->cdbr(left_reg, kDoubleRegZero);
  /* left == right != 0. */
  assm->bne(&return_left, Label::kNear);
  /* At this point, both left and right are either 0 or -0. */
  /* N.B. The following works because +0 + -0 == +0 */
  /* For max we want logical-and of sign bit: (L + R) */
  assm->ldr(result_reg, left_reg);
  assm->adbr(result_reg, right_reg);
  assm->b(&done, Label::kNear);

  assm->bind(&check_nan_left);
  assm->cdbr(left_reg, left_reg);
  /* left == NaN. */
  assm->bunordered(&return_left, Label::kNear);

  assm->bind(&return_right);
  if (right_reg != result_reg) {
    assm->ldr(result_reg, right_reg);
  }
  assm->b(&done, Label::kNear);

  assm->bind(&return_left);
  if (left_reg != result_reg) {
    assm->ldr(result_reg, left_reg);
  }
  assm->bind(&done);
}

inline void DoubleMin(LiftoffAssembler* assm, DoubleRegister result_reg,
                      DoubleRegister left_reg, DoubleRegister right_reg) {
  Label check_nan_left, check_zero, return_left, return_right, done;
  assm->cdbr(left_reg, right_reg);
  assm->bunordered(&check_nan_left, Label::kNear);
  assm->beq(&check_zero);
  assm->ble(&return_left, Label::kNear);
  assm->b(&return_right, Label::kNear);

  assm->bind(&check_zero);
  assm->lzdr(kDoubleRegZero);
  assm->cdbr(left_reg, kDoubleRegZero);
  /* left == right != 0. */
  assm->bne(&return_left, Label::kNear);
  /* At this point, both left and right are either 0 or -0. */
  /* N.B. The following works because +0 + -0 == +0 */
  /* For min we want logical-or of sign bit: -(-L + -R) */
  assm->lcdbr(left_reg, left_reg);
  assm->ldr(result_reg, left_reg);
  if (left_reg == right_reg) {
    assm->adbr(result_reg, right_reg);
  } else {
    assm->sdbr(result_reg, right_reg);
  }
  assm->lcdbr(result_reg, result_reg);
  assm->b(&done, Label::kNear);

  assm->bind(&check_nan_left);
  assm->cdbr(left_reg, left_reg);
  /* left == NaN. */
  assm->bunordered(&return_left, Label::kNear);

  assm->bind(&return_right);
  if (right_reg != result_reg) {
    assm->ldr(result_reg, right_reg);
  }
  assm->b(&done, Label::kNear);

  assm->bind(&return_left);
  if (left_reg != result_reg) {
    assm->ldr(result_reg, left_reg);
  }
  assm->bind(&done);
}

}  // namespace liftoff

int LiftoffAssembler::PrepareStackFrame() {
  int offset = pc_offset();
  lay(sp, MemOperand(sp, -0));
  return offset;
}

void LiftoffAssembler::PrepareTailCall(int num_callee_stack_params,
                                       int stack_param_delta) {
  bailout(kUnsupportedArchitecture, "PrepareTailCall");
}

void LiftoffAssembler::PatchPrepareStackFrame(int offset, int frame_size) {
  // Need to align sp to system pointer size.
  frame_size = RoundUp(frame_size, 8);
  constexpr int kAvailableSpace = 64;
  Assembler patching_assembler(
      AssemblerOptions{},
      ExternalAssemblerBuffer(buffer_start_ + offset, kAvailableSpace));
  patching_assembler.lay(sp, MemOperand(sp, -frame_size));
}

void LiftoffAssembler::FinishCode() {}

void LiftoffAssembler::AbortCompilation() { AbortedCodeGeneration(); }

// static
constexpr int LiftoffAssembler::StaticStackFrameSize() {
  return liftoff::kInstanceOffset;
}

int LiftoffAssembler::SlotSizeForType(ValueType type) {
  switch (type.kind()) {
    case ValueType::kS128:
      return type.element_size_bytes();
    default:
      return kStackSlotSize;
  }
}

bool LiftoffAssembler::NeedsAlignment(ValueType type) {
  return (type.kind() == ValueType::kS128 || type.is_reference_type());
}

void LiftoffAssembler::LoadConstant(LiftoffRegister reg, WasmValue value,
                                    RelocInfo::Mode rmode) {
  switch (value.type().kind()) {
    case ValueType::kI32:
      mov(reg.gp(), Operand(value.to_i32(), rmode));
      break;
    case ValueType::kI64:
      DCHECK(RelocInfo::IsNone(rmode));
      TurboAssembler::Load(reg.gp(), Operand(value.to_i64()));
      break;
    case ValueType::kF32: {
      UseScratchRegisterScope temps(this);
      Register scratch = temps.Acquire();
      LoadFloat32Literal(reg.fp(), value.to_f32_boxed().get_scalar(), scratch);
      break;
    }
    case ValueType::kF64: {
      UseScratchRegisterScope temps(this);
      Register scratch = temps.Acquire();
      uint64_t int_val =
          bit_cast<uint64_t, double>(value.to_f64_boxed().get_scalar());
      LoadDoubleLiteral(reg.fp(), int_val, scratch);
      break;
    }
    default:
      UNREACHABLE();
  }
}

void LiftoffAssembler::LoadFromInstance(Register dst, uint32_t offset,
                                        int size) {
  DCHECK_LE(offset, kMaxInt);
  LoadP(dst, liftoff::GetInstanceOperand());
  DCHECK(size == 4 || size == 8);
  if (size == 4) {
    LoadW(dst, MemOperand(dst, offset));
  } else {
    LoadP(dst, MemOperand(dst, offset));
  }
}

void LiftoffAssembler::LoadTaggedPointerFromInstance(Register dst,
                                                     uint32_t offset) {
  LoadFromInstance(dst, offset, kTaggedSize);
}

void LiftoffAssembler::SpillInstance(Register instance) {
  StoreP(instance, liftoff::GetInstanceOperand());
}

void LiftoffAssembler::FillInstanceInto(Register dst) {
  LoadP(dst, liftoff::GetInstanceOperand());
}

void LiftoffAssembler::LoadTaggedPointer(Register dst, Register src_addr,
                                         Register offset_reg,
                                         int32_t offset_imm,
                                         LiftoffRegList pinned) {
  STATIC_ASSERT(kTaggedSize == kInt64Size);
  Load(LiftoffRegister(dst), src_addr, offset_reg, offset_imm,
       LoadType::kI64Load, pinned);
}

void LiftoffAssembler::StoreTaggedPointer(Register dst_addr,
                                          int32_t offset_imm,
                                          LiftoffRegister src,
                                          LiftoffRegList pinned) {
  bailout(kRefTypes, "GlobalSet");
}

void LiftoffAssembler::Load(LiftoffRegister dst, Register src_addr,
                            Register offset_reg, uint32_t offset_imm,
                            LoadType type, LiftoffRegList pinned,
                            uint32_t* protected_load_pc, bool is_load_mem) {
  UseScratchRegisterScope temps(this);
  MemOperand src_op =
      liftoff::GetMemOp(this, &temps, src_addr, offset_reg, offset_imm);
  if (protected_load_pc) *protected_load_pc = pc_offset();
  bool change_endianness_load = false;
#if defined(V8_TARGET_BIG_ENDIAN)
  if (is_load_mem) {
    change_endianness_load = true;
  }
#endif
  if (change_endianness_load) {
    switch (type.value()) {
      case LoadType::kI32Load8U:
      case LoadType::kI64Load8U:
        LoadlB(dst.gp(), src_op);
        break;
      case LoadType::kI32Load8S:
      case LoadType::kI64Load8S:
        LoadB(dst.gp(), src_op);
        break;
      case LoadType::kI32Load16U:
      case LoadType::kI64Load16U:
        LoadLogicalReversedHalfWordP(dst.gp(), src_op);
        break;
      case LoadType::kI32Load16S:
      case LoadType::kI64Load16S:
        lrvh(dst.gp(), src_op);
        lghr(dst.gp(), dst.gp());
        break;
      case LoadType::kI64Load32U:
        LoadLogicalReversedWordP(dst.gp(), src_op);
        break;
      case LoadType::kI32Load:
      case LoadType::kI64Load32S:
        lrv(dst.gp(), src_op);
        lgfr(dst.gp(), dst.gp());
        break;
      case LoadType::kI64Load:
        lrvg(dst.gp(), src_op);
        break;
      case LoadType::kF32Load:
        lrv(r0, src_op);
        MovIntToFloat(dst.fp(), r0);
        break;
      case LoadType::kF64Load:
        lrvg(r0, src_op);
        ldgr(dst.fp(), r0);
        break;
      case LoadType::kS128Load: {
        MemOperand operand = src_op;
        if (CpuFeatures::IsSupported(VECTOR_ENHANCE_FACILITY_2)) {
          vlbr(dst.fp(), operand, Condition(4));
        } else {
          lrvg(r0, operand);
          lrvg(r1, MemOperand(operand.rx(), operand.rb(),
                              operand.offset() + kBitsPerByte));
          vlvgp(dst.fp(), r1, r0);
        }
        break;
      }
      default:
        UNREACHABLE();
    }
  } else {
    switch (type.value()) {
      case LoadType::kI32Load8U:
      case LoadType::kI64Load8U:
        LoadlB(dst.gp(), src_op);
        break;
      case LoadType::kI32Load8S:
      case LoadType::kI64Load8S:
        LoadB(dst.gp(), src_op);
        break;
      case LoadType::kI32Load16U:
      case LoadType::kI64Load16U:
        LoadLogicalHalfWordP(dst.gp(), src_op);
        break;
      case LoadType::kI32Load16S:
      case LoadType::kI64Load16S:
        LoadHalfWordP(dst.gp(), src_op);
        break;
      case LoadType::kI64Load32U:
        LoadlW(dst.gp(), src_op);
        break;
      case LoadType::kI32Load:
      case LoadType::kI64Load32S:
        LoadW(dst.gp(), src_op);
        break;
      case LoadType::kI64Load:
        LoadP(dst.gp(), src_op);
        break;
      case LoadType::kF32Load:
        LoadFloat32(dst.fp(), src_op);
        break;
      case LoadType::kF64Load:
        LoadDouble(dst.fp(), src_op);
        break;
      case LoadType::kS128Load: {
        UseScratchRegisterScope temps(this);
        Register scratch = temps.Acquire();
        LoadSimd128(dst.fp(), src_op, scratch);
        break;
      }
      default:
        UNREACHABLE();
    }
  }
}

void LiftoffAssembler::Store(Register dst_addr, Register offset_reg,
                             uint32_t offset_imm, LiftoffRegister src,
                             StoreType type, LiftoffRegList pinned,
                             uint32_t* protected_store_pc, bool is_store_mem) {
  UseScratchRegisterScope temps(this);
  MemOperand dst_op =
      liftoff::GetMemOp(this, &temps, dst_addr, offset_reg, offset_imm);
  if (protected_store_pc) *protected_store_pc = pc_offset();
  bool change_endianness_store = false;
#if defined(V8_TARGET_BIG_ENDIAN)
  if (is_store_mem) {
    change_endianness_store = true;
  }
#endif
  if (change_endianness_store) {
    switch (type.value()) {
      case StoreType::kI64Store8:
      case StoreType::kI32Store8:
        StoreByte(src.gp(), dst_op);
        break;
      case StoreType::kI32Store16:
      case StoreType::kI64Store16:
        strvh(src.gp(), dst_op);
        break;
      case StoreType::kI64Store:
        strvg(src.gp(), dst_op);
        break;
      case StoreType::kI32Store:
      case StoreType::kI64Store32:
        strv(src.gp(), dst_op);
        break;
      case StoreType::kF32Store: {
        MovFloatToInt(r0, src.fp());
        lrvr(r0, r0);
        MovIntToFloat(kScratchDoubleReg, r0);
        StoreFloat32(kScratchDoubleReg, dst_op);
        break;
      }
      case StoreType::kF64Store: {
        lgdr(r0, src.fp());
        lrvgr(r0, r0);
        ldgr(kScratchDoubleReg, r0);
        StoreDouble(kScratchDoubleReg, dst_op);
        break;
      }
      case StoreType::kS128Store: {
        MemOperand operand = dst_op;
        if (CpuFeatures::IsSupported(VECTOR_ENHANCE_FACILITY_2)) {
          vstbr(src.fp(), operand, Condition(4));
        } else {
          vlgv(r0, src.fp(), MemOperand(r0, 1), Condition(3));
          vlgv(r1, src.fp(), MemOperand(r0, 0), Condition(3));
          strvg(r0, operand);
          strvg(r1, MemOperand(operand.rx(), operand.rb(),
                               operand.offset() + kBitsPerByte));
        }
        break;
      }
      default:
        UNREACHABLE();
    }
  } else {
    switch (type.value()) {
      case StoreType::kI32Store8:
      case StoreType::kI64Store8:
        stc(src.gp(), dst_op);
        break;
      case StoreType::kI32Store16:
      case StoreType::kI64Store16:
        StoreHalfWord(src.gp(), dst_op);
        break;
      case StoreType::kI32Store:
      case StoreType::kI64Store32:
        StoreW(src.gp(), dst_op);
        break;
      case StoreType::kI64Store:
        StoreP(src.gp(), dst_op);
        break;
      case StoreType::kF32Store:
        StoreFloat32(src.fp(), dst_op);
        break;
      case StoreType::kF64Store:
        StoreDouble(src.fp(), dst_op);
        break;
      case StoreType::kS128Store: {
        UseScratchRegisterScope temps(this);
        Register scratch = temps.Acquire();
        StoreSimd128(src.fp(), dst_op, scratch);
        break;
      }
      default:
        UNREACHABLE();
    }
  }
}

void LiftoffAssembler::AtomicLoad(LiftoffRegister dst, Register src_addr,
                                  Register offset_reg, uint32_t offset_imm,
                                  LoadType type, LiftoffRegList pinned) {
  bailout(kAtomics, "AtomicLoad");
}

void LiftoffAssembler::AtomicStore(Register dst_addr, Register offset_reg,
                                   uint32_t offset_imm, LiftoffRegister src,
                                   StoreType type, LiftoffRegList pinned) {
  bailout(kAtomics, "AtomicStore");
}

void LiftoffAssembler::AtomicAdd(Register dst_addr, Register offset_reg,
                                 uint32_t offset_imm, LiftoffRegister value,
                                 LiftoffRegister result, StoreType type) {
  bailout(kAtomics, "AtomicAdd");
}

void LiftoffAssembler::AtomicSub(Register dst_addr, Register offset_reg,
                                 uint32_t offset_imm, LiftoffRegister value,
                                 LiftoffRegister result, StoreType type) {
  bailout(kAtomics, "AtomicSub");
}

void LiftoffAssembler::AtomicAnd(Register dst_addr, Register offset_reg,
                                 uint32_t offset_imm, LiftoffRegister value,
                                 LiftoffRegister result, StoreType type) {
  bailout(kAtomics, "AtomicAnd");
}

void LiftoffAssembler::AtomicOr(Register dst_addr, Register offset_reg,
                                uint32_t offset_imm, LiftoffRegister value,
                                LiftoffRegister result, StoreType type) {
  bailout(kAtomics, "AtomicOr");
}

void LiftoffAssembler::AtomicXor(Register dst_addr, Register offset_reg,
                                 uint32_t offset_imm, LiftoffRegister value,
                                 LiftoffRegister result, StoreType type) {
  bailout(kAtomics, "AtomicXor");
}

void LiftoffAssembler::AtomicExchange(Register dst_addr, Register offset_reg,
                                      uint32_t offset_imm,
                                      LiftoffRegister value,
                                      LiftoffRegister result, StoreType type) {
  bailout(kAtomics, "AtomicExchange");
}

void LiftoffAssembler::AtomicCompareExchange(
    Register dst_addr, Register offset_reg, uint32_t offset_imm,
    LiftoffRegister expected, LiftoffRegister new_value, LiftoffRegister result,
    StoreType type) {
  bailout(kAtomics, "AtomicCompareExchange");
}

void LiftoffAssembler::AtomicFence() { bailout(kAtomics, "AtomicFence"); }

void LiftoffAssembler::LoadCallerFrameSlot(LiftoffRegister dst,
                                           uint32_t caller_slot_idx,
                                           ValueType type) {
  int32_t offset = (caller_slot_idx + 1) * 8;
  switch (type.kind()) {
    case ValueType::kI32: {
#if defined(V8_TARGET_BIG_ENDIAN)
      LoadW(dst.gp(), MemOperand(fp, offset + 4));
      break;
#else
      LoadW(dst.gp(), MemOperand(fp, offset));
      break;
#endif
    }
    case ValueType::kI64: {
      LoadP(dst.gp(), MemOperand(fp, offset));
      break;
    }
    case ValueType::kF32: {
#if defined(V8_TARGET_BIG_ENDIAN)
      LoadFloat32(dst.fp(), MemOperand(fp, offset));
      break;
#else
      LoadFloat32(dst.fp(), MemOperand(fp, offset + 4));
      break;
#endif
    }
    case ValueType::kF64: {
      LoadDouble(dst.fp(), MemOperand(fp, offset));
      break;
    }
    case ValueType::kS128: {
      UseScratchRegisterScope temps(this);
      Register scratch = temps.Acquire();
      LoadSimd128(dst.fp(), MemOperand(fp, offset), scratch);
      break;
    }
    default:
      UNREACHABLE();
  }
}

void LiftoffAssembler::StoreCallerFrameSlot(LiftoffRegister src,
                                            uint32_t caller_slot_idx,
                                            ValueType type) {
  bailout(kUnsupportedArchitecture, "StoreCallerFrameSlot");
}

void LiftoffAssembler::LoadReturnStackSlot(LiftoffRegister dst, int offset,
                                           ValueType type) {
  bailout(kUnsupportedArchitecture, "LoadReturnStackSlot");
}

void LiftoffAssembler::MoveStackValue(uint32_t dst_offset, uint32_t src_offset,
                                      ValueType type) {
  DCHECK_NE(dst_offset, src_offset);
  LiftoffRegister reg = GetUnusedRegister(reg_class_for(type));
  Fill(reg, src_offset, type);
  Spill(dst_offset, reg, type);
}

void LiftoffAssembler::Move(Register dst, Register src, ValueType type) {
  if (type == kWasmI32) {
    lr(dst, src);
  } else {
    DCHECK_EQ(kWasmI64, type);
    TurboAssembler::Move(dst, src);
  }
}

void LiftoffAssembler::Move(DoubleRegister dst, DoubleRegister src,
                            ValueType type) {
  DCHECK_NE(dst, src);
  if (type == kWasmF32) {
    ler(dst, src);
  } else if (type == kWasmF64) {
    ldr(dst, src);
  } else {
    DCHECK_EQ(kWasmS128, type);
    vlr(dst, src, Condition(0), Condition(0), Condition(0));
  }
}

void LiftoffAssembler::Spill(int offset, LiftoffRegister reg, ValueType type) {
  RecordUsedSpillOffset(offset);
  MemOperand dst = liftoff::GetStackSlot(offset);
  switch (type.kind()) {
    case ValueType::kI32:
      StoreW(reg.gp(), dst);
      break;
    case ValueType::kI64:
      StoreP(reg.gp(), dst);
      break;
    case ValueType::kF32:
      StoreFloat32(reg.fp(), dst);
      break;
    case ValueType::kF64:
      StoreDouble(reg.fp(), dst);
      break;
    case ValueType::kS128: {
      UseScratchRegisterScope temps(this);
      Register scratch = temps.Acquire();
      StoreSimd128(reg.fp(), dst, scratch);
      break;
    }
    default:
      UNREACHABLE();
  }
}

void LiftoffAssembler::Spill(int offset, WasmValue value) {
  RecordUsedSpillOffset(offset);
  MemOperand dst = liftoff::GetStackSlot(offset);
  UseScratchRegisterScope temps(this);
  Register src = no_reg;
  if (!is_uint12(abs(dst.offset()))) {
    src = GetUnusedRegister(kGpReg).gp();
  } else {
    src = temps.Acquire();
  }
  switch (value.type().kind()) {
    case ValueType::kI32: {
      TurboAssembler::Load(src, Operand(value.to_i32()));
      StoreW(src, dst);
      break;
    }
    case ValueType::kI64: {
      TurboAssembler::Load(src, Operand(value.to_i64()));
      StoreP(src, dst);
      break;
    }
    default:
      // We do not track f32 and f64 constants, hence they are unreachable.
      UNREACHABLE();
  }
}

void LiftoffAssembler::Fill(LiftoffRegister reg, int offset, ValueType type) {
  MemOperand src = liftoff::GetStackSlot(offset);
  switch (type.kind()) {
    case ValueType::kI32:
      LoadW(reg.gp(), src);
      break;
    case ValueType::kI64:
      LoadP(reg.gp(), src);
      break;
    case ValueType::kF32:
      LoadFloat32(reg.fp(), src);
      break;
    case ValueType::kF64:
      LoadDouble(reg.fp(), src);
      break;
    case ValueType::kS128: {
      UseScratchRegisterScope temps(this);
      Register scratch = temps.Acquire();
      LoadSimd128(reg.fp(), src, scratch);
      break;
    }
    default:
      UNREACHABLE();
  }
}

void LiftoffAssembler::FillI64Half(Register, int offset, RegPairHalf) {
  UNREACHABLE();
}

void LiftoffAssembler::FillStackSlotsWithZero(int start, int size) {
  DCHECK_LT(0, size);
  DCHECK_EQ(0, size % 4);
  RecordUsedSpillOffset(start + size);

  // We need a zero reg. Always use r0 for that, and push it before to restore
  // its value afterwards.
  push(r0);
  lgfi(r0, Operand(0));

  if (size <= 5 * kStackSlotSize) {
    // Special straight-line code for up to five slots. Generates two
    // instructions per slot.
    uint32_t remainder = size;
    for (; remainder >= kStackSlotSize; remainder -= kStackSlotSize) {
      StoreP(r0, liftoff::GetStackSlot(start + remainder));
    }
    DCHECK(remainder == 4 || remainder == 0);
    if (remainder) {
      StoreW(r0, liftoff::GetStackSlot(start + remainder));
    }
  } else {
    // General case for bigger counts (9 instructions).
    // Use r3 for start address (inclusive), r4 for end address (exclusive).
    push(r3);
    push(r4);

    lay(r3, MemOperand(fp, -start - size));
    lay(r4, MemOperand(fp, -start));

    Label loop;
    bind(&loop);
    StoreP(r0, MemOperand(r3));
    lay(r3, MemOperand(r3, kSystemPointerSize));
    CmpLogicalP(r3, r4);
    bne(&loop);
    pop(r4);
    pop(r3);
  }

  pop(r0);
}

#define I32_BINOP(name, instruction)                             \
  void LiftoffAssembler::emit_##name(Register dst, Register lhs, \
                                     Register rhs) {             \
    instruction(dst, lhs, rhs);                                  \
  }
#define I32_BINOP_I(name, instruction)                              \
  I32_BINOP(name, instruction)                                      \
  void LiftoffAssembler::emit_##name##i(Register dst, Register lhs, \
                                        int32_t imm) {              \
    instruction(dst, lhs, Operand(imm));                            \
  }
#define I64_BINOP(name, instruction)                                           \
  void LiftoffAssembler::emit_##name(LiftoffRegister dst, LiftoffRegister lhs, \
                                     LiftoffRegister rhs) {                    \
    instruction(dst.gp(), lhs.gp(), rhs.gp());                                 \
  }
#define I64_BINOP_I(name, instruction)                                      \
  I64_BINOP(name, instruction)                                              \
  void LiftoffAssembler::emit_##name##i(LiftoffRegister dst,                \
                                        LiftoffRegister lhs, int32_t imm) { \
    instruction(dst.gp(), lhs.gp(), Operand(imm));                          \
  }
#define FP32_BINOP(name, instruction)                                        \
  void LiftoffAssembler::emit_##name(DoubleRegister dst, DoubleRegister lhs, \
                                     DoubleRegister rhs) {                   \
    ler(dst, lhs);                                                           \
    instruction(dst, rhs);                                                   \
  }
#define FP32_UNOP(name, instruction)                                           \
  void LiftoffAssembler::emit_##name(DoubleRegister dst, DoubleRegister src) { \
    instruction(dst, src);                                                     \
  }
#define FP64_BINOP(name, instruction)                                        \
  void LiftoffAssembler::emit_##name(DoubleRegister dst, DoubleRegister lhs, \
                                     DoubleRegister rhs) {                   \
    ldr(dst, lhs);                                                           \
    instruction(dst, rhs);                                                   \
  }
#define FP64_UNOP(name, instruction)                                           \
  void LiftoffAssembler::emit_##name(DoubleRegister dst, DoubleRegister src) { \
    instruction(dst, src);                                                     \
  }
#define I32_SHIFTOP(name, instruction)                              \
  void LiftoffAssembler::emit_##name(Register dst, Register src,    \
                                     Register amount) {             \
    LoadRR(r1, amount);                                             \
    And(r1, Operand(0x1f));                                         \
    instruction(dst, src, r1);                                      \
  }                                                                 \
  void LiftoffAssembler::emit_##name##i(Register dst, Register src, \
                                        int32_t amount) {           \
    instruction(dst, src, Operand(amount & 31));                    \
  }
#define I64_SHIFTOP(name, instruction)                                         \
  void LiftoffAssembler::emit_##name(LiftoffRegister dst, LiftoffRegister src, \
                                     Register amount) {                        \
    instruction(dst.gp(), src.gp(), amount);                                   \
  }                                                                            \
  void LiftoffAssembler::emit_##name##i(LiftoffRegister dst,                   \
                                        LiftoffRegister src, int32_t amount) { \
    instruction(dst.gp(), src.gp(), Operand(amount & 63));                     \
  }

I32_BINOP_I(i32_add, Add32)
I32_BINOP(i32_sub, Sub32)
I32_BINOP(i32_mul, Mul)
I32_BINOP_I(i32_and, And)
I32_BINOP_I(i32_or, Or)
I32_BINOP_I(i32_xor, Xor)
I32_SHIFTOP(i32_shl, ShiftLeft)
I32_SHIFTOP(i32_sar, ShiftRightArith)
I32_SHIFTOP(i32_shr, ShiftRight)
I64_BINOP_I(i64_add, AddP)
I64_BINOP(i64_sub, SubP)
I64_BINOP(i64_mul, Mul)
#ifdef V8_TARGET_ARCH_S390X
I64_BINOP_I(i64_and, AndP)
I64_BINOP_I(i64_or, OrP)
I64_BINOP_I(i64_xor, XorP)
#endif
I64_SHIFTOP(i64_shl, ShiftLeftP)
I64_SHIFTOP(i64_sar, ShiftRightArithP)
I64_SHIFTOP(i64_shr, ShiftRightP)
FP32_BINOP(f32_add, aebr)
FP32_BINOP(f32_sub, sebr)
FP32_BINOP(f32_mul, meebr)
FP32_BINOP(f32_div, debr)
FP32_UNOP(f32_abs, lpebr)
FP32_UNOP(f32_neg, lcebr)
FP32_UNOP(f32_sqrt, sqebr)
FP64_BINOP(f64_add, adbr)
FP64_BINOP(f64_sub, sdbr)
FP64_BINOP(f64_mul, mdbr)
FP64_BINOP(f64_div, ddbr)
FP64_UNOP(f64_abs, lpdbr)
FP64_UNOP(f64_neg, lcdbr)
FP64_UNOP(f64_sqrt, sqdbr)

void LiftoffAssembler::emit_i32_clz(Register dst, Register src) {
  llgfr(dst, src);
  flogr(r0, dst);
  Add32(dst, r0, Operand(-32));
}

void LiftoffAssembler::emit_i32_ctz(Register dst, Register src) {
  Label cont;
  Label done;
  // Check if src is all zeros.
  Cmp32(src, Operand(0));
  bne(&cont);
  lhi(dst, Operand(32));
  beq(&done);

  bind(&cont);
  llgfr(src, src);
  lcgr(r0, src);
  ngr(src, r0);
  flogr(r0, src);
  lghi(r1, Operand(63));
  SubP(dst, r1, r0);
  bind(&done);
}

bool LiftoffAssembler::emit_i32_popcnt(Register dst, Register src) {
  Popcnt32(dst, src);
  return true;
}

bool LiftoffAssembler::emit_i64_popcnt(LiftoffRegister dst,
                                       LiftoffRegister src) {
  Popcnt64(dst.gp(), src.gp());
  return true;
}

bool LiftoffAssembler::emit_f32_ceil(DoubleRegister dst, DoubleRegister src) {
  fiebra(v8::internal::Assembler::FIDBRA_ROUND_TOWARD_POS_INF, dst, src);
  return true;
}

bool LiftoffAssembler::emit_f32_floor(DoubleRegister dst, DoubleRegister src) {
  fiebra(v8::internal::Assembler::FIDBRA_ROUND_TOWARD_NEG_INF, dst, src);
  return true;
}

bool LiftoffAssembler::emit_f32_trunc(DoubleRegister dst, DoubleRegister src) {
  fiebra(v8::internal::Assembler::FIDBRA_ROUND_TOWARD_0, dst, src);
  return true;
}

bool LiftoffAssembler::emit_f32_nearest_int(DoubleRegister dst,
                                            DoubleRegister src) {
  fiebra(v8::internal::Assembler::FIDBRA_ROUND_TO_NEAREST_TO_EVEN, dst, src);
  return true;
}

void LiftoffAssembler::emit_f32_min(DoubleRegister dst, DoubleRegister lhs,
                                    DoubleRegister rhs) {
  liftoff::FloatMin(this, dst, lhs, rhs);
}

void LiftoffAssembler::emit_f32_max(DoubleRegister dst, DoubleRegister lhs,
                                    DoubleRegister rhs) {
  liftoff::FloatMax(this, dst, lhs, rhs);
}

bool LiftoffAssembler::emit_f64_ceil(DoubleRegister dst, DoubleRegister src) {
  fidbra(v8::internal::Assembler::FIDBRA_ROUND_TOWARD_POS_INF, dst, src);
  return true;
}

bool LiftoffAssembler::emit_f64_floor(DoubleRegister dst, DoubleRegister src) {
  fidbra(v8::internal::Assembler::FIDBRA_ROUND_TOWARD_NEG_INF, dst, src);
  return true;
}

bool LiftoffAssembler::emit_f64_trunc(DoubleRegister dst, DoubleRegister src) {
  fidbra(v8::internal::Assembler::FIDBRA_ROUND_TOWARD_0, dst, src);
  return true;
}

bool LiftoffAssembler::emit_f64_nearest_int(DoubleRegister dst,
                                            DoubleRegister src) {
  fidbra(v8::internal::Assembler::FIDBRA_ROUND_TO_NEAREST_TO_EVEN, dst, src);
  return true;
}

void LiftoffAssembler::emit_f64_min(DoubleRegister dst, DoubleRegister lhs,
                                    DoubleRegister rhs) {
  liftoff::DoubleMin(this, dst, lhs, rhs);
}

void LiftoffAssembler::emit_f64_max(DoubleRegister dst, DoubleRegister lhs,
                                    DoubleRegister rhs) {
  liftoff::DoubleMax(this, dst, lhs, rhs);
}

void LiftoffAssembler::emit_i32_divs(Register dst, Register lhs, Register rhs,
                                     Label* trap_div_by_zero,
                                     Label* trap_div_unrepresentable) {
  Label cont;

  // Check for division by zero.
  Cmp32(rhs, Operand(0));
  b(eq, trap_div_by_zero);

  // Check for kMinInt / -1. This is unrepresentable.
  Cmp32(rhs, Operand(-1));
  bne(&cont);
  Cmp32(lhs, Operand(kMinInt));
  b(eq, trap_div_unrepresentable);

  bind(&cont);
  Div32(dst, lhs, rhs);
}

void LiftoffAssembler::emit_i32_divu(Register dst, Register lhs, Register rhs,
                                     Label* trap_div_by_zero) {
  // Check for division by zero.
  Cmp32(rhs, Operand(0));
  beq(trap_div_by_zero);
  DivU32(dst, lhs, rhs);
}

void LiftoffAssembler::emit_i32_rems(Register dst, Register lhs, Register rhs,
                                     Label* trap_div_by_zero) {
  Label cont;
  Label done;
  Label trap_div_unrepresentable;
  // Check for division by zero.
  Cmp32(rhs, Operand(0));
  beq(trap_div_by_zero);

  // Check kMinInt/-1 case.
  Cmp32(rhs, Operand(-1));
  bne(&cont);
  Cmp32(lhs, Operand(kMinInt));
  beq(&trap_div_unrepresentable);

  // Continue noraml calculation.
  bind(&cont);
  Mod32(dst, lhs, rhs);
  bne(&done);

  // trap by kMinInt/-1 case.
  bind(&trap_div_unrepresentable);
  mov(dst, Operand(0));
  bind(&done);
}

void LiftoffAssembler::emit_i32_remu(Register dst, Register lhs, Register rhs,
                                     Label* trap_div_by_zero) {
  // Check for division by zero.
  Cmp32(rhs, Operand(0));
  beq(trap_div_by_zero);
  ModU32(dst, lhs, rhs);
}

bool LiftoffAssembler::emit_i64_divs(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs,
                                     Label* trap_div_by_zero,
                                     Label* trap_div_unrepresentable) {
  // Use r0 to check for kMinInt / -1.
  iilf(r0, Operand(0));
  iihf(r0, Operand(kMinInt));
  Label cont;
  // Check for division by zero.
  CmpP(rhs.gp(), Operand(0));
  beq(trap_div_by_zero);

  // Check for kMinInt / -1. This is unrepresentable.
  CmpP(rhs.gp(), Operand(-1));
  bne(&cont);
  CmpP(lhs.gp(), r0);
  b(eq, trap_div_unrepresentable);

  bind(&cont);
  Div64(dst.gp(), lhs.gp(), rhs.gp());
  return true;
}

bool LiftoffAssembler::emit_i64_divu(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs,
                                     Label* trap_div_by_zero) {
  CmpP(rhs.gp(), Operand(0));
  b(eq, trap_div_by_zero);
  // Do div.
  DivU64(dst.gp(), lhs.gp(), rhs.gp());
  return true;
}

bool LiftoffAssembler::emit_i64_rems(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs,
                                     Label* trap_div_by_zero) {
  Label trap_div_unrepresentable;
  Label done;
  Label cont;

  // Use r0 to check for kMinInt / -1.
  iilf(r0, Operand(0));
  iihf(r0, Operand(kMinInt));

  // Check for division by zero.
  CmpP(rhs.gp(), Operand(0));
  beq(trap_div_by_zero);

  // Check for kMinInt / -1. This is unrepresentable.
  CmpP(rhs.gp(), Operand(-1));
  bne(&cont);
  CmpP(lhs.gp(), r0);
  beq(&trap_div_unrepresentable);

  bind(&cont);
  Mod64(dst.gp(), lhs.gp(), rhs.gp());
  bne(&done);

  bind(&trap_div_unrepresentable);
  mov(dst.gp(), Operand(0));
  bind(&done);
  return true;
}

bool LiftoffAssembler::emit_i64_remu(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs,
                                     Label* trap_div_by_zero) {
  // Check for division by zero.
  CmpP(rhs.gp(), Operand(0));
  beq(trap_div_by_zero);
  ModU64(dst.gp(), lhs.gp(), rhs.gp());
  return true;
}

void LiftoffAssembler::emit_i64_clz(LiftoffRegister dst, LiftoffRegister src) {
  flogr(r0, src.gp());
  LoadRR(dst.gp(), r0);
}

void LiftoffAssembler::emit_i64_ctz(LiftoffRegister dst, LiftoffRegister src) {
  Label cont;
  Label done;
  CmpP(src.gp(), Operand(0));
  bne(&cont);
  lghi(dst.gp(), Operand(64));
  beq(&done);

  bind(&cont);
  lcgr(r0, src.gp());
  ngr(src.gp(), r0);
  flogr(r0, src.gp());
  lghi(r1, Operand(63));
  SubP(dst.gp(), r1, r0);
  bind(&done);
}

void LiftoffAssembler::emit_u32_to_intptr(Register dst, Register src) {
#ifdef V8_TARGET_ARCH_S390X
  LoadlW(dst, src);
#endif
}

void LiftoffAssembler::emit_f32_copysign(DoubleRegister dst, DoubleRegister lhs,
                                         DoubleRegister rhs) {
  constexpr uint64_t kF64SignBit = uint64_t{1} << 63;
  UseScratchRegisterScope temps(this);
  Register scratch2 = temps.Acquire();
  MovDoubleToInt64(r0, lhs);
  // Clear sign bit in {r0}.
  AndP(r0, Operand(~kF64SignBit));

  MovDoubleToInt64(scratch2, rhs);
  // Isolate sign bit in {scratch2}.
  AndP(scratch2, Operand(kF64SignBit));
  // Combine {scratch2} into {r0}.
  OrP(r0, r0, scratch2);
  MovInt64ToDouble(dst, r0);
}

void LiftoffAssembler::emit_f64_copysign(DoubleRegister dst, DoubleRegister lhs,
                                         DoubleRegister rhs) {
  constexpr uint64_t kF64SignBit = uint64_t{1} << 63;
  UseScratchRegisterScope temps(this);
  Register scratch2 = temps.Acquire();
  MovDoubleToInt64(r0, lhs);
  // Clear sign bit in {r0}.
  AndP(r0, Operand(~kF64SignBit));

  MovDoubleToInt64(scratch2, rhs);
  // Isolate sign bit in {scratch2}.
  AndP(scratch2, Operand(kF64SignBit));
  // Combine {scratch2} into {r0}.
  OrP(r0, r0, scratch2);
  MovInt64ToDouble(dst, r0);
}

bool LiftoffAssembler::emit_type_conversion(WasmOpcode opcode,
                                            LiftoffRegister dst,
                                            LiftoffRegister src, Label* trap) {
  switch (opcode) {
    case kExprI32ConvertI64:
      lgfr(dst.gp(), src.gp());
      return true;
    case kExprI32SConvertF32: {
      ConvertFloat32ToInt32(dst.gp(), src.fp(),
                            kRoundToZero);  // f32 -> i32 round to zero.
      b(Condition(1), trap);
      return true;
    }
    case kExprI32UConvertF32: {
#if defined(V8_TARGET_BIG_ENDIAN)
      ConvertFloat32ToUnsignedInt32(dst.gp(), src.fp());
#else
      ldebr(src.fp(), src.fp());
      fidbra(v8::internal::Assembler::FIDBRA_ROUND_TOWARD_0, src.fp(),
             src.fp());
      ConvertDoubleToUnsignedInt32(dst.gp(),
                                   src.fp());  // f32 -> i32 round to zero.
#endif
      b(Condition(1), trap);
      return true;
    }
    case kExprI32SConvertF64: {
#if defined(V8_TARGET_BIG_ENDIAN)
      ConvertDoubleToInt32(dst.gp(), src.fp());
#else
      fidbra(v8::internal::Assembler::FIDBRA_ROUND_TOWARD_0, src.fp(),
             src.fp());
      ConvertDoubleToInt32(dst.gp(), src.fp());  // f64 -> i32 round to zero.
#endif
      b(Condition(1), trap);
      return true;
    }
    case kExprI32UConvertF64: {
#if defined(V8_TARGET_BIG_ENDIAN)
      ConvertDoubleToUnsignedInt32(dst.gp(), src.fp());
#else
      fidbra(v8::internal::Assembler::FIDBRA_ROUND_TOWARD_0, src.fp(),
             src.fp());
      ConvertDoubleToUnsignedInt32(dst.gp(),
                                   src.fp());  // f64 -> i32 round to zero.
#endif
      b(Condition(1), trap);
      return true;
    }
    case kExprI32ReinterpretF32:
      lgdr(dst.gp(), src.fp());
      srlg(dst.gp(), dst.gp(), Operand(32));
      return true;
    case kExprI64SConvertI32:
      LoadW(dst.gp(), src.gp());
      return true;
    case kExprI64UConvertI32:
      llgfr(dst.gp(), src.gp());
      return true;
    case kExprI64ReinterpretF64:
      lgdr(dst.gp(), src.fp());
      return true;
    case kExprF32SConvertI32: {
      ConvertIntToFloat(dst.fp(), src.gp());
      return true;
    }
    case kExprF32UConvertI32: {
      ConvertUnsignedIntToFloat(dst.fp(), src.gp());
      return true;
    }
    case kExprF32ConvertF64:
      ledbr(dst.fp(), src.fp());
      return true;
    case kExprF32ReinterpretI32: {
      sllg(r0, src.gp(), Operand(32));
      ldgr(dst.fp(), r0);
      return true;
    }
    case kExprF64SConvertI32: {
      ConvertIntToDouble(dst.fp(), src.gp());
      return true;
    }
    case kExprF64UConvertI32: {
      ConvertUnsignedIntToDouble(dst.fp(), src.gp());
      return true;
    }
    case kExprF64ConvertF32:
      ldebr(dst.fp(), src.fp());
      return true;
    case kExprF64ReinterpretI64:
      ldgr(dst.fp(), src.gp());
      return true;
    case kExprF64SConvertI64:
      ConvertInt64ToDouble(dst.fp(), src.gp());
      return true;
    case kExprF64UConvertI64:
      ConvertUnsignedInt64ToDouble(dst.fp(), src.gp());
      return true;
    case kExprI64SConvertF32: {
      ConvertFloat32ToInt64(dst.gp(), src.fp());  // f32 -> i64 round to zero.
      b(Condition(1), trap);
      return true;
    }
    case kExprI64UConvertF32: {
      Label done;
      ConvertFloat32ToUnsignedInt64(dst.gp(),
                                    src.fp());  // f32 -> i64 round to zero.
      b(Condition(1), trap);
      b(Condition(0xE), &done, Label::kNear);
      lghi(dst.gp(), Operand::Zero());
      bind(&done);
      return true;
    }
    case kExprF32SConvertI64:
      ConvertInt64ToFloat(dst.fp(), src.gp());
      return true;
    case kExprF32UConvertI64:
      ConvertUnsignedInt64ToFloat(dst.fp(), src.gp());
      return true;
    case kExprI64SConvertF64: {
      ConvertDoubleToInt64(dst.gp(), src.fp());  // f64 -> i64 round to zero.
      b(Condition(1), trap);
      return true;
    }
    case kExprI64UConvertF64: {
      ConvertDoubleToUnsignedInt64(dst.gp(),
                                   src.fp());  // f64 -> i64 round to zero.
      b(Condition(1), trap);
      return true;
    }
    default:
      UNREACHABLE();
  }
}

void LiftoffAssembler::emit_i32_signextend_i8(Register dst, Register src) {
  lbr(dst, src);
}

void LiftoffAssembler::emit_i32_signextend_i16(Register dst, Register src) {
  lhr(dst, src);
}

void LiftoffAssembler::emit_i64_signextend_i8(LiftoffRegister dst,
                                              LiftoffRegister src) {
  LoadB(dst.gp(), src.gp());
}

void LiftoffAssembler::emit_i64_signextend_i16(LiftoffRegister dst,
                                               LiftoffRegister src) {
  LoadHalfWordP(dst.gp(), src.gp());
}

void LiftoffAssembler::emit_i64_signextend_i32(LiftoffRegister dst,
                                               LiftoffRegister src) {
  LoadW(dst.gp(), src.gp());
}

void LiftoffAssembler::emit_jump(Label* label) { b(al, label); }

void LiftoffAssembler::emit_jump(Register target) { Jump(target); }

void LiftoffAssembler::emit_cond_jump(Condition cond, Label* label,
                                      ValueType type, Register lhs,
                                      Register rhs) {
  Condition liftoff_cond = liftoff::LiftoffCondToCond(cond);
  switch (type.kind()) {
    case ValueType::kI32: {
      rhs == no_reg
          ? (liftoff_cond == cond ? CmpLogical32(lhs, Operand(0))
                                  : Cmp32(lhs, Operand(0)))
          : (liftoff_cond == cond ? CmpLogical32(lhs, rhs) : Cmp32(lhs, rhs));
      break;
    }
    case ValueType::kI64: {
      rhs == no_reg
          ? (liftoff_cond == cond ? CmpLogicalP(lhs, Operand(0))
                                  : CmpP(lhs, Operand(0)))
          : (liftoff_cond == cond ? CmpLogicalP(lhs, rhs) : CmpP(lhs, rhs));
      break;
    }
    default:
      UNREACHABLE();
  }
  b(liftoff_cond, label);
}

void LiftoffAssembler::emit_i32_eqz(Register dst, Register src) {
  emit_i32_clz(dst, src);
  ShiftRight(dst, dst, Operand(5));
}

void LiftoffAssembler::emit_i32_set_cond(Condition cond, Register dst,
                                         Register lhs, Register rhs) {
  Condition liftoff_cond = liftoff::LiftoffCondToCond(cond);
  liftoff_cond != cond ? Cmp32(lhs, rhs) : CmpLogical32(lhs, rhs);
  lghi(dst, Operand(0));
  lghi(r0, Operand(1));
  locr(liftoff_cond, dst, r0);
}

void LiftoffAssembler::emit_i64_eqz(Register dst, LiftoffRegister src) {
  Label done;
  lghi(dst, Operand(0));
  CmpP(src.gp(), Operand(0));
  bne(&done);
  lghi(dst, Operand(1));
  bind(&done);
}

void LiftoffAssembler::emit_i64_set_cond(Condition cond, Register dst,
                                         LiftoffRegister lhs,
                                         LiftoffRegister rhs) {
  Condition liftoff_cond = liftoff::LiftoffCondToCond(cond);
  UseScratchRegisterScope temps(this);
  Register scratch = temps.Acquire();
  liftoff_cond == cond ? CmpLogicalP(lhs.gp(), rhs.gp())
                       : CmpP(lhs.gp(), rhs.gp());
  lghi(dst, Operand(0));
  lghi(scratch, Operand(1));
  LoadOnConditionP(liftoff_cond, dst, scratch);
}

void LiftoffAssembler::emit_f32_set_cond(Condition cond, Register dst,
                                         DoubleRegister lhs,
                                         DoubleRegister rhs) {
  cond = liftoff::LiftoffCondToCond(cond);
  UseScratchRegisterScope temps(this);
  Register scratch = temps.Acquire();
  lghi(dst, Operand(0));
  lghi(scratch, Operand(1));
  cebr(lhs, rhs);
  LoadOnConditionP(cond, dst, scratch);
  if (cond != ne) {
    lghi(scratch, Operand(0));
    LoadOnConditionP(overflow, dst, scratch);
  }
}

void LiftoffAssembler::emit_f64_set_cond(Condition cond, Register dst,
                                         DoubleRegister lhs,
                                         DoubleRegister rhs) {
  cond = liftoff::LiftoffCondToCond(cond);
  UseScratchRegisterScope temps(this);
  Register scratch = temps.Acquire();
  lghi(dst, Operand(0));
  lghi(scratch, Operand(1));
  cdbr(lhs, rhs);
  LoadOnConditionP(cond, dst, scratch);
  if (cond != ne) {
    lghi(scratch, Operand(0));
    LoadOnConditionP(overflow, dst, scratch);
  }
}

bool LiftoffAssembler::emit_select(LiftoffRegister dst, Register condition,
                                   LiftoffRegister true_value,
                                   LiftoffRegister false_value,
                                   ValueType type) {
  return false;
}

void LiftoffAssembler::LoadTransform(LiftoffRegister dst, Register src_addr,
                                     Register offset_reg, uint32_t offset_imm,
                                     LoadType type,
                                     LoadTransformationKind transform,
                                     uint32_t* protected_load_pc) {
  bailout(kSimd, "Load transform unimplemented");
}

void LiftoffAssembler::emit_i8x16_swizzle(LiftoffRegister dst,
                                          LiftoffRegister lhs,
                                          LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_swizzle");
}

void LiftoffAssembler::emit_f64x2_splat(LiftoffRegister dst,
                                        LiftoffRegister src) {
  vrep(dst.fp(), src.fp(), Operand(0), Condition(3));
}

void LiftoffAssembler::emit_f64x2_extract_lane(LiftoffRegister dst,
                                               LiftoffRegister lhs,
                                               uint8_t imm_lane_idx) {
#ifdef V8_TARGET_BIG_ENDIAN
  vrep(dst.fp(), lhs.fp(), Operand(1 - imm_lane_idx), Condition(3));
#else
  vrep(dst.fp(), lhs.fp(), Operand(imm_lane_idx), Condition(3));
#endif
}

void LiftoffAssembler::emit_f64x2_replace_lane(LiftoffRegister dst,
                                               LiftoffRegister src1,
                                               LiftoffRegister src2,
                                               uint8_t imm_lane_idx) {
  bailout(kUnsupportedArchitecture, "emit_f64x2replacelane");
}

void LiftoffAssembler::emit_f64x2_abs(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_f64x2_abs");
}

void LiftoffAssembler::emit_f64x2_neg(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_f64x2neg");
}

void LiftoffAssembler::emit_f64x2_sqrt(LiftoffRegister dst,
                                       LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_f64x2sqrt");
}

bool LiftoffAssembler::emit_f64x2_ceil(LiftoffRegister dst,
                                       LiftoffRegister src) {
  bailout(kSimd, "f64x2.ceil");
  return true;
}

bool LiftoffAssembler::emit_f64x2_floor(LiftoffRegister dst,
                                        LiftoffRegister src) {
  bailout(kSimd, "f64x2.floor");
  return true;
}

bool LiftoffAssembler::emit_f64x2_trunc(LiftoffRegister dst,
                                        LiftoffRegister src) {
  bailout(kSimd, "f64x2.trunc");
  return true;
}

bool LiftoffAssembler::emit_f64x2_nearest_int(LiftoffRegister dst,
                                              LiftoffRegister src) {
  bailout(kSimd, "f64x2.nearest_int");
  return true;
}

void LiftoffAssembler::emit_f64x2_add(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  vfa(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(3));
}

void LiftoffAssembler::emit_f64x2_sub(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  vfs(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(3));
}

void LiftoffAssembler::emit_f64x2_mul(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f64x2mul");
}

void LiftoffAssembler::emit_f64x2_div(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f64x2div");
}

void LiftoffAssembler::emit_f64x2_min(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f64x2min");
}

void LiftoffAssembler::emit_f64x2_max(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f64x2max");
}

void LiftoffAssembler::emit_f64x2_pmin(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kSimd, "pmin unimplemented");
}

void LiftoffAssembler::emit_f64x2_pmax(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kSimd, "pmax unimplemented");
}

void LiftoffAssembler::emit_f32x4_splat(LiftoffRegister dst,
                                        LiftoffRegister src) {
#ifdef V8_TARGET_BIG_ENDIAN
  vrep(dst.fp(), src.fp(), Operand(0), Condition(2));
#else
  vrep(dst.fp(), src.fp(), Operand(1), Condition(2));
#endif
}

void LiftoffAssembler::emit_f32x4_extract_lane(LiftoffRegister dst,
                                               LiftoffRegister lhs,
                                               uint8_t imm_lane_idx) {
#ifdef V8_TARGET_BIG_ENDIAN
  vrep(dst.fp(), lhs.fp(), Operand(3 - imm_lane_idx), Condition(2));
#else
  vrep(dst.fp(), lhs.fp(), Operand(imm_lane_idx), Condition(2));
#endif
}

void LiftoffAssembler::emit_f32x4_replace_lane(LiftoffRegister dst,
                                               LiftoffRegister src1,
                                               LiftoffRegister src2,
                                               uint8_t imm_lane_idx) {
  bailout(kUnsupportedArchitecture, "emit_f32x4replacelane");
}

void LiftoffAssembler::emit_f32x4_abs(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_f32x4_abs");
}

void LiftoffAssembler::emit_f32x4_neg(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_f32x4neg");
}

void LiftoffAssembler::emit_f32x4_sqrt(LiftoffRegister dst,
                                       LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_f32x4sqrt");
}

bool LiftoffAssembler::emit_f32x4_ceil(LiftoffRegister dst,
                                       LiftoffRegister src) {
  bailout(kSimd, "f32x4.ceil");
  return true;
}

bool LiftoffAssembler::emit_f32x4_floor(LiftoffRegister dst,
                                        LiftoffRegister src) {
  bailout(kSimd, "f32x4.floor");
  return true;
}

bool LiftoffAssembler::emit_f32x4_trunc(LiftoffRegister dst,
                                        LiftoffRegister src) {
  bailout(kSimd, "f32x4.trunc");
  return true;
}

bool LiftoffAssembler::emit_f32x4_nearest_int(LiftoffRegister dst,
                                              LiftoffRegister src) {
  bailout(kSimd, "f32x4.nearest_int");
  return true;
}

void LiftoffAssembler::emit_f32x4_add(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  vfa(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(2));
}

void LiftoffAssembler::emit_f32x4_sub(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  vfs(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(2));
}

void LiftoffAssembler::emit_f32x4_mul(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f32x4mul");
}

void LiftoffAssembler::emit_f32x4_div(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f32x4div");
}

void LiftoffAssembler::emit_f32x4_min(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f32x4min");
}

void LiftoffAssembler::emit_f32x4_max(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f32x4max");
}

void LiftoffAssembler::emit_f32x4_pmin(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kSimd, "pmin unimplemented");
}

void LiftoffAssembler::emit_f32x4_pmax(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kSimd, "pmax unimplemented");
}

void LiftoffAssembler::emit_i64x2_splat(LiftoffRegister dst,
                                        LiftoffRegister src) {
  vlvg(dst.fp(), src.gp(), MemOperand(r0, 0), Condition(3));
  vrep(dst.fp(), dst.fp(), Operand(0), Condition(3));
}

void LiftoffAssembler::emit_i64x2_extract_lane(LiftoffRegister dst,
                                               LiftoffRegister lhs,
                                               uint8_t imm_lane_idx) {
#ifdef V8_TARGET_BIG_ENDIAN
  vlgv(dst.gp(), lhs.fp(), MemOperand(r0, 1 - imm_lane_idx), Condition(3));
#else
  vlgv(dst.gp(), lhs.fp(), MemOperand(r0, imm_lane_idx), Condition(3));
#endif
}

void LiftoffAssembler::emit_i64x2_replace_lane(LiftoffRegister dst,
                                               LiftoffRegister src1,
                                               LiftoffRegister src2,
                                               uint8_t imm_lane_idx) {
  bailout(kUnsupportedArchitecture, "emit_i64x2replacelane");
}

void LiftoffAssembler::emit_i64x2_neg(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i64x2neg");
}

void LiftoffAssembler::emit_i64x2_shl(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kSimd, "i64x2_shl");
}

void LiftoffAssembler::emit_i64x2_shli(LiftoffRegister dst, LiftoffRegister lhs,
                                       int32_t rhs) {
  bailout(kSimd, "i64x2_shli");
}

void LiftoffAssembler::emit_i64x2_shr_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kSimd, "i64x2_shr_s");
}

void LiftoffAssembler::emit_i64x2_shri_s(LiftoffRegister dst,
                                         LiftoffRegister lhs, int32_t rhs) {
  bailout(kSimd, "i64x2_shri_s");
}

void LiftoffAssembler::emit_i64x2_shr_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kSimd, "i64x2_shr_u");
}

void LiftoffAssembler::emit_i64x2_shri_u(LiftoffRegister dst,
                                         LiftoffRegister lhs, int32_t rhs) {
  bailout(kSimd, "i64x2_shri_u");
}

void LiftoffAssembler::emit_i64x2_add(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  va(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(3));
}

void LiftoffAssembler::emit_i64x2_sub(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  vs(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(3));
}

void LiftoffAssembler::emit_i64x2_mul(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i64x2mul");
}

void LiftoffAssembler::emit_i32x4_splat(LiftoffRegister dst,
                                        LiftoffRegister src) {
  vlvg(dst.fp(), src.gp(), MemOperand(r0, 0), Condition(2));
  vrep(dst.fp(), dst.fp(), Operand(0), Condition(2));
}

void LiftoffAssembler::emit_i32x4_extract_lane(LiftoffRegister dst,
                                               LiftoffRegister lhs,
                                               uint8_t imm_lane_idx) {
#ifdef V8_TARGET_BIG_ENDIAN
  vlgv(dst.gp(), lhs.fp(), MemOperand(r0, 3 - imm_lane_idx), Condition(2));
#else
  vlgv(dst.gp(), lhs.fp(), MemOperand(r0, imm_lane_idx), Condition(2));
#endif
}

void LiftoffAssembler::emit_i32x4_replace_lane(LiftoffRegister dst,
                                               LiftoffRegister src1,
                                               LiftoffRegister src2,
                                               uint8_t imm_lane_idx) {
  bailout(kUnsupportedArchitecture, "emit_i32x4replacelane");
}

void LiftoffAssembler::emit_i32x4_neg(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i32x4neg");
}

void LiftoffAssembler::emit_v32x4_anytrue(LiftoffRegister dst,
                                          LiftoffRegister src) {
  bailout(kSimd, "v32x4_anytrue");
}

void LiftoffAssembler::emit_v32x4_alltrue(LiftoffRegister dst,
                                          LiftoffRegister src) {
  bailout(kSimd, "v32x4_alltrue");
}

void LiftoffAssembler::emit_i32x4_bitmask(LiftoffRegister dst,
                                          LiftoffRegister src) {
  bailout(kSimd, "i32x4_bitmask");
}

void LiftoffAssembler::emit_i32x4_shl(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kSimd, "i32x4_shl");
}

void LiftoffAssembler::emit_i32x4_shli(LiftoffRegister dst, LiftoffRegister lhs,
                                       int32_t rhs) {
  bailout(kSimd, "i32x4_shli");
}

void LiftoffAssembler::emit_i32x4_shr_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kSimd, "i32x4_shr_s");
}

void LiftoffAssembler::emit_i32x4_shri_s(LiftoffRegister dst,
                                         LiftoffRegister lhs, int32_t rhs) {
  bailout(kSimd, "i32x4_shri_s");
}

void LiftoffAssembler::emit_i32x4_shr_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kSimd, "i32x4_shr_u");
}

void LiftoffAssembler::emit_i32x4_shri_u(LiftoffRegister dst,
                                         LiftoffRegister lhs, int32_t rhs) {
  bailout(kSimd, "i32x4_shri_u");
}

void LiftoffAssembler::emit_i32x4_add(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  va(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(2));
}

void LiftoffAssembler::emit_i32x4_sub(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  vs(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(2));
}

void LiftoffAssembler::emit_i32x4_mul(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4mul");
}

void LiftoffAssembler::emit_i32x4_min_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_min_s");
}

void LiftoffAssembler::emit_i32x4_min_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_min_u");
}

void LiftoffAssembler::emit_i32x4_max_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_max_s");
}

void LiftoffAssembler::emit_i32x4_max_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_max_u");
}

void LiftoffAssembler::emit_i16x8_splat(LiftoffRegister dst,
                                        LiftoffRegister src) {
  vlvg(dst.fp(), src.gp(), MemOperand(r0, 0), Condition(1));
  vrep(dst.fp(), dst.fp(), Operand(0), Condition(1));
}

void LiftoffAssembler::emit_i16x8_neg(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i16x8neg");
}

void LiftoffAssembler::emit_v16x8_anytrue(LiftoffRegister dst,
                                          LiftoffRegister src) {
  bailout(kSimd, "v16x8_anytrue");
}

void LiftoffAssembler::emit_v16x8_alltrue(LiftoffRegister dst,
                                          LiftoffRegister src) {
  bailout(kSimd, "v16x8_alltrue");
}

void LiftoffAssembler::emit_i16x8_bitmask(LiftoffRegister dst,
                                          LiftoffRegister src) {
  bailout(kSimd, "i16x8_bitmask");
}

void LiftoffAssembler::emit_i16x8_shl(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kSimd, "i16x8_shl");
}

void LiftoffAssembler::emit_i16x8_shli(LiftoffRegister dst, LiftoffRegister lhs,
                                       int32_t rhs) {
  bailout(kSimd, "i16x8_shli");
}

void LiftoffAssembler::emit_i16x8_shr_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kSimd, "i16x8_shr_s");
}

void LiftoffAssembler::emit_i16x8_shri_s(LiftoffRegister dst,
                                         LiftoffRegister lhs, int32_t rhs) {
  bailout(kSimd, "i16x8_shri_s");
}

void LiftoffAssembler::emit_i16x8_shr_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kSimd, "i16x8_shr_u");
}

void LiftoffAssembler::emit_i16x8_shri_u(LiftoffRegister dst,
                                         LiftoffRegister lhs, int32_t rhs) {
  bailout(kSimd, "i16x8_shri_u");
}

void LiftoffAssembler::emit_i16x8_add(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  va(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(1));
}

void LiftoffAssembler::emit_i16x8_add_saturate_s(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8addsaturate_s");
}

void LiftoffAssembler::emit_i16x8_sub(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  vs(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(1));
}

void LiftoffAssembler::emit_i16x8_sub_saturate_s(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8subsaturate_s");
}

void LiftoffAssembler::emit_i16x8_sub_saturate_u(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8subsaturate_u");
}

void LiftoffAssembler::emit_i16x8_mul(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8mul");
}

void LiftoffAssembler::emit_i16x8_add_saturate_u(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8addsaturate_u");
}

void LiftoffAssembler::emit_i16x8_min_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_min_s");
}

void LiftoffAssembler::emit_i16x8_min_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_min_u");
}

void LiftoffAssembler::emit_i16x8_max_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_max_s");
}

void LiftoffAssembler::emit_i16x8_max_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_max_u");
}

void LiftoffAssembler::emit_i16x8_extract_lane_u(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 uint8_t imm_lane_idx) {
#ifdef V8_TARGET_BIG_ENDIAN
  vlgv(dst.gp(), lhs.fp(), MemOperand(r0, 7 - imm_lane_idx), Condition(1));
#else
  vlgv(dst.gp(), lhs.fp(), MemOperand(r0, imm_lane_idx), Condition(1));
#endif
}

void LiftoffAssembler::emit_i16x8_replace_lane(LiftoffRegister dst,
                                               LiftoffRegister src1,
                                               LiftoffRegister src2,
                                               uint8_t imm_lane_idx) {
  bailout(kUnsupportedArchitecture, "emit_i16x8replacelane");
}

void LiftoffAssembler::emit_i16x8_extract_lane_s(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 uint8_t imm_lane_idx) {
  UseScratchRegisterScope temps(this);
  Register scratch = temps.Acquire();
#ifdef V8_TARGET_BIG_ENDIAN
  vlgv(scratch, lhs.fp(), MemOperand(r0, 7 - imm_lane_idx), Condition(1));
#else
  vlgv(scratch, lhs.fp(), MemOperand(r0, imm_lane_idx), Condition(1));
#endif
  lghr(dst.gp(), scratch);
}

void LiftoffAssembler::emit_i8x16_shuffle(LiftoffRegister dst,
                                          LiftoffRegister lhs,
                                          LiftoffRegister rhs,
                                          const uint8_t shuffle[16],
                                          bool is_swizzle) {
  bailout(kSimd, "i8x16_shuffle");
}

void LiftoffAssembler::emit_i8x16_splat(LiftoffRegister dst,
                                        LiftoffRegister src) {
  vlvg(dst.fp(), src.gp(), MemOperand(r0, 0), Condition(0));
  vrep(dst.fp(), dst.fp(), Operand(0), Condition(0));
}

void LiftoffAssembler::emit_i8x16_extract_lane_u(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 uint8_t imm_lane_idx) {
#ifdef V8_TARGET_BIG_ENDIAN
  vlgv(dst.gp(), lhs.fp(), MemOperand(r0, 15 - imm_lane_idx), Condition(0));
#else
  vlgv(dst.gp(), lhs.fp(), MemOperand(r0, imm_lane_idx), Condition(0));
#endif
}

void LiftoffAssembler::emit_i8x16_extract_lane_s(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 uint8_t imm_lane_idx) {
  UseScratchRegisterScope temps(this);
  Register scratch = temps.Acquire();
#ifdef V8_TARGET_BIG_ENDIAN
  vlgv(scratch, lhs.fp(), MemOperand(r0, 15 - imm_lane_idx), Condition(0));
#else
  vlgv(scratch, lhs.fp(), MemOperand(r0, imm_lane_idx), Condition(0));
#endif
  lgbr(dst.gp(), scratch);
}

void LiftoffAssembler::emit_i8x16_replace_lane(LiftoffRegister dst,
                                               LiftoffRegister src1,
                                               LiftoffRegister src2,
                                               uint8_t imm_lane_idx) {
  bailout(kUnsupportedArchitecture, "emit_i8x16replacelane");
}

void LiftoffAssembler::emit_i8x16_neg(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i8x16neg");
}

void LiftoffAssembler::emit_v8x16_anytrue(LiftoffRegister dst,
                                          LiftoffRegister src) {
  bailout(kSimd, "v8x16_anytrue");
}

void LiftoffAssembler::emit_v8x16_alltrue(LiftoffRegister dst,
                                          LiftoffRegister src) {
  bailout(kSimd, "v8x16_alltrue");
}

void LiftoffAssembler::emit_i8x16_bitmask(LiftoffRegister dst,
                                          LiftoffRegister src) {
  bailout(kSimd, "i8x16_bitmask");
}

void LiftoffAssembler::emit_i8x16_shl(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kSimd, "i8x16_shl");
}

void LiftoffAssembler::emit_i8x16_shli(LiftoffRegister dst, LiftoffRegister lhs,
                                       int32_t rhs) {
  bailout(kSimd, "i8x16_shli");
}

void LiftoffAssembler::emit_i8x16_shr_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kSimd, "i8x16_shr_s");
}

void LiftoffAssembler::emit_i8x16_shri_s(LiftoffRegister dst,
                                         LiftoffRegister lhs, int32_t rhs) {
  bailout(kSimd, "i8x16_shri_s");
}

void LiftoffAssembler::emit_i8x16_shr_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kSimd, "i8x16_shr_u");
}

void LiftoffAssembler::emit_i8x16_shri_u(LiftoffRegister dst,
                                         LiftoffRegister lhs, int32_t rhs) {
  bailout(kSimd, "i8x16_shri_u");
}

void LiftoffAssembler::emit_i8x16_add(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  va(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(0));
}

void LiftoffAssembler::emit_i8x16_add_saturate_s(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16addsaturate_s");
}

void LiftoffAssembler::emit_i8x16_sub(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  vs(dst.fp(), lhs.fp(), rhs.fp(), Condition(0), Condition(0), Condition(0));
}

void LiftoffAssembler::emit_i8x16_sub_saturate_s(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16subsaturate_s");
}

void LiftoffAssembler::emit_i8x16_sub_saturate_u(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16subsaturate_u");
}

void LiftoffAssembler::emit_i8x16_mul(LiftoffRegister dst, LiftoffRegister lhs,
                                      LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16mul");
}

void LiftoffAssembler::emit_i8x16_add_saturate_u(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16addsaturate_u");
}

void LiftoffAssembler::emit_i8x16_min_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_min_s");
}

void LiftoffAssembler::emit_i8x16_min_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_min_u");
}

void LiftoffAssembler::emit_i8x16_max_s(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_max_s");
}

void LiftoffAssembler::emit_i8x16_max_u(LiftoffRegister dst,
                                        LiftoffRegister lhs,
                                        LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_max_u");
}

void LiftoffAssembler::emit_i8x16_eq(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_eq");
}

void LiftoffAssembler::emit_i8x16_ne(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_ne");
}

void LiftoffAssembler::emit_i8x16_gt_s(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16gt_s");
}

void LiftoffAssembler::emit_i8x16_gt_u(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16gt_u");
}

void LiftoffAssembler::emit_i8x16_ge_s(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16ge_s");
}

void LiftoffAssembler::emit_i8x16_ge_u(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16ge_u");
}

void LiftoffAssembler::emit_i16x8_eq(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_eq");
}

void LiftoffAssembler::emit_i16x8_ne(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_ne");
}

void LiftoffAssembler::emit_i16x8_gt_s(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8gt_s");
}

void LiftoffAssembler::emit_i16x8_gt_u(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8gt_u");
}

void LiftoffAssembler::emit_i16x8_ge_s(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8ge_s");
}

void LiftoffAssembler::emit_i16x8_ge_u(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8ge_u");
}

void LiftoffAssembler::emit_i32x4_eq(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_eq");
}

void LiftoffAssembler::emit_i32x4_ne(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_ne");
}

void LiftoffAssembler::emit_i32x4_gt_s(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4gt_s");
}

void LiftoffAssembler::emit_i32x4_gt_u(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4gt_u");
}

void LiftoffAssembler::emit_i32x4_ge_s(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4ge_s");
}

void LiftoffAssembler::emit_i32x4_ge_u(LiftoffRegister dst, LiftoffRegister lhs,
                                       LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i32x4ge_u");
}

void LiftoffAssembler::emit_f32x4_eq(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f32x4_eq");
}

void LiftoffAssembler::emit_f32x4_ne(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f32x4_ne");
}

void LiftoffAssembler::emit_f32x4_lt(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f32x4_lt");
}

void LiftoffAssembler::emit_f32x4_le(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f32x4_le");
}

void LiftoffAssembler::emit_f64x2_eq(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f64x2_eq");
}

void LiftoffAssembler::emit_f64x2_ne(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f64x2_ne");
}

void LiftoffAssembler::emit_f64x2_lt(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f64x2_lt");
}

void LiftoffAssembler::emit_f64x2_le(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_f64x2_le");
}

void LiftoffAssembler::emit_s128_const(LiftoffRegister dst,
                                       const uint8_t imms[16]) {
  bailout(kUnsupportedArchitecture, "emit_s128_const");
}

void LiftoffAssembler::emit_s128_not(LiftoffRegister dst, LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_s128_not");
}

void LiftoffAssembler::emit_s128_and(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_s128_and");
}

void LiftoffAssembler::emit_s128_or(LiftoffRegister dst, LiftoffRegister lhs,
                                    LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_s128_or");
}

void LiftoffAssembler::emit_s128_xor(LiftoffRegister dst, LiftoffRegister lhs,
                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_s128_xor");
}

void LiftoffAssembler::emit_s128_select(LiftoffRegister dst,
                                        LiftoffRegister src1,
                                        LiftoffRegister src2,
                                        LiftoffRegister mask) {
  bailout(kUnsupportedArchitecture, "emit_s128select");
}

void LiftoffAssembler::emit_i32x4_sconvert_f32x4(LiftoffRegister dst,
                                                 LiftoffRegister src) {
  bailout(kSimd, "i32x4_sconvert_f32x4");
}

void LiftoffAssembler::emit_i32x4_uconvert_f32x4(LiftoffRegister dst,
                                                 LiftoffRegister src) {
  bailout(kSimd, "i32x4_uconvert_f32x4");
}

void LiftoffAssembler::emit_f32x4_sconvert_i32x4(LiftoffRegister dst,
                                                 LiftoffRegister src) {
  bailout(kSimd, "f32x4_sconvert_i32x4");
}

void LiftoffAssembler::emit_f32x4_uconvert_i32x4(LiftoffRegister dst,
                                                 LiftoffRegister src) {
  bailout(kSimd, "f32x4_uconvert_i32x4");
}

void LiftoffAssembler::emit_i8x16_sconvert_i16x8(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_sconvert_i16x8");
}

void LiftoffAssembler::emit_i8x16_uconvert_i16x8(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_uconvert_i16x8");
}

void LiftoffAssembler::emit_i16x8_sconvert_i32x4(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_sconvert_i32x4");
}

void LiftoffAssembler::emit_i16x8_uconvert_i32x4(LiftoffRegister dst,
                                                 LiftoffRegister lhs,
                                                 LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_uconvert_i32x4");
}

void LiftoffAssembler::emit_i16x8_sconvert_i8x16_low(LiftoffRegister dst,
                                                     LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_sconvert_i8x16_low");
}

void LiftoffAssembler::emit_i16x8_sconvert_i8x16_high(LiftoffRegister dst,
                                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_sconvert_i8x16_high");
}

void LiftoffAssembler::emit_i16x8_uconvert_i8x16_low(LiftoffRegister dst,
                                                     LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_uconvert_i8x16_low");
}

void LiftoffAssembler::emit_i16x8_uconvert_i8x16_high(LiftoffRegister dst,
                                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_uconvert_i8x16_high");
}

void LiftoffAssembler::emit_i32x4_sconvert_i16x8_low(LiftoffRegister dst,
                                                     LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_sconvert_i16x8_low");
}

void LiftoffAssembler::emit_i32x4_sconvert_i16x8_high(LiftoffRegister dst,
                                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_sconvert_i16x8_high");
}

void LiftoffAssembler::emit_i32x4_uconvert_i16x8_low(LiftoffRegister dst,
                                                     LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_uconvert_i16x8_low");
}

void LiftoffAssembler::emit_i32x4_uconvert_i16x8_high(LiftoffRegister dst,
                                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_uconvert_i16x8_high");
}

void LiftoffAssembler::emit_s128_and_not(LiftoffRegister dst,
                                         LiftoffRegister lhs,
                                         LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_s128_and_not");
}

void LiftoffAssembler::emit_i8x16_rounding_average_u(LiftoffRegister dst,
                                                     LiftoffRegister lhs,
                                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_rounding_average_u");
}

void LiftoffAssembler::emit_i16x8_rounding_average_u(LiftoffRegister dst,
                                                     LiftoffRegister lhs,
                                                     LiftoffRegister rhs) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_rounding_average_u");
}

void LiftoffAssembler::emit_i8x16_abs(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i8x16_abs");
}

void LiftoffAssembler::emit_i16x8_abs(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i16x8_abs");
}

void LiftoffAssembler::emit_i32x4_abs(LiftoffRegister dst,
                                      LiftoffRegister src) {
  bailout(kUnsupportedArchitecture, "emit_i32x4_abs");
}

void LiftoffAssembler::StackCheck(Label* ool_code, Register limit_address) {
  LoadP(limit_address, MemOperand(limit_address));
  CmpLogicalP(sp, limit_address);
  b(le, ool_code);
}

void LiftoffAssembler::CallTrapCallbackForTesting() {
  PrepareCallCFunction(0, 0, no_reg);
  CallCFunction(ExternalReference::wasm_call_trap_callback_for_testing(), 0);
}

void LiftoffAssembler::AssertUnreachable(AbortReason reason) {
  // Asserts unreachable within the wasm code.
  TurboAssembler::AssertUnreachable(reason);
}

void LiftoffAssembler::PushRegisters(LiftoffRegList regs) {
  MultiPush(regs.GetGpList());
  MultiPushDoubles(regs.GetFpList());
}

void LiftoffAssembler::PopRegisters(LiftoffRegList regs) {
  MultiPop(regs.GetGpList());
  MultiPopDoubles(regs.GetFpList());
}

void LiftoffAssembler::DropStackSlotsAndRet(uint32_t num_stack_slots) {
  Drop(num_stack_slots);
  Ret();
}

void LiftoffAssembler::CallC(const wasm::FunctionSig* sig,
                             const LiftoffRegister* args,
                             const LiftoffRegister* rets,
                             ValueType out_argument_type, int stack_bytes,
                             ExternalReference ext_ref) {
  int total_size = RoundUp(stack_bytes, 8);
  // Reserve space in the stack.
  lay(sp, MemOperand(sp, -total_size));

  int arg_bytes = 0;
  for (ValueType param_type : sig->parameters()) {
    switch (param_type.kind()) {
      case ValueType::kI32:
        StoreW(args->gp(), MemOperand(sp, arg_bytes));
        break;
      case ValueType::kI64:
        StoreP(args->gp(), MemOperand(sp, arg_bytes));
        break;
      case ValueType::kF32:
        StoreFloat32(args->fp(), MemOperand(sp, arg_bytes));
        break;
      case ValueType::kF64:
        StoreDouble(args->fp(), MemOperand(sp, arg_bytes));
        break;
      default:
        UNREACHABLE();
    }
    args++;
    arg_bytes += param_type.element_size_bytes();
  }

  DCHECK_LE(arg_bytes, stack_bytes);

  // Pass a pointer to the buffer with the arguments to the C function.
  LoadRR(r2, sp);

  // Now call the C function.
  constexpr int kNumCCallArgs = 1;
  PrepareCallCFunction(kNumCCallArgs, no_reg);
  CallCFunction(ext_ref, kNumCCallArgs);

  // Move return value to the right register.
  const LiftoffRegister* result_reg = rets;
  if (sig->return_count() > 0) {
    DCHECK_EQ(1, sig->return_count());
    constexpr Register kReturnReg = r2;
    if (kReturnReg != rets->gp()) {
      Move(*rets, LiftoffRegister(kReturnReg), sig->GetReturn(0));
    }
    result_reg++;
  }

  // Load potential output value from the buffer on the stack.
  if (out_argument_type != kWasmStmt) {
    switch (out_argument_type.kind()) {
      case ValueType::kI32:
        LoadW(result_reg->gp(), MemOperand(sp));
        break;
      case ValueType::kI64:
        LoadP(result_reg->gp(), MemOperand(sp));
        break;
      case ValueType::kF32:
        LoadFloat32(result_reg->fp(), MemOperand(sp));
        break;
      case ValueType::kF64:
        LoadDouble(result_reg->fp(), MemOperand(sp));
        break;
      default:
        UNREACHABLE();
    }
  }
  lay(sp, MemOperand(sp, total_size));
}

void LiftoffAssembler::CallNativeWasmCode(Address addr) {
  Call(addr, RelocInfo::WASM_CALL);
}

void LiftoffAssembler::TailCallNativeWasmCode(Address addr) {
  bailout(kUnsupportedArchitecture, "TailCallNativeWasmCode");
}

void LiftoffAssembler::CallIndirect(const wasm::FunctionSig* sig,
                                    compiler::CallDescriptor* call_descriptor,
                                    Register target) {
  DCHECK(target != no_reg);
  Call(target);
}

void LiftoffAssembler::TailCallIndirect(Register target) {
  bailout(kUnsupportedArchitecture, "TailCallIndirect");
}

void LiftoffAssembler::CallRuntimeStub(WasmCode::RuntimeStubId sid) {
  // A direct call to a wasm runtime stub defined in this module.
  // Just encode the stub index. This will be patched at relocation.
  Call(static_cast<Address>(sid), RelocInfo::WASM_STUB_CALL);
}

void LiftoffAssembler::AllocateStackSlot(Register addr, uint32_t size) {
  lay(sp, MemOperand(sp, -size));
  TurboAssembler::Move(addr, sp);
}

void LiftoffAssembler::DeallocateStackSlot(uint32_t size) {
  lay(sp, MemOperand(sp, size));
}

void LiftoffStackSlots::Construct() {
  for (auto& slot : slots_) {
    const LiftoffAssembler::VarState& src = slot.src_;
    switch (src.loc()) {
      case LiftoffAssembler::VarState::kStack: {
        switch (src.type().kind()) {
          case ValueType::kI32:
          case ValueType::kI64: {
            UseScratchRegisterScope temps(asm_);
            Register scratch = temps.Acquire();
            asm_->LoadP(scratch, liftoff::GetStackSlot(slot.src_offset_));
            asm_->Push(scratch);
            break;
          }
          case ValueType::kF32: {
            asm_->LoadFloat32(kScratchDoubleReg,
                              liftoff::GetStackSlot(slot.src_offset_));
            asm_->push(kScratchDoubleReg);
            break;
          }
          case ValueType::kF64: {
            asm_->LoadDouble(kScratchDoubleReg,
                             liftoff::GetStackSlot(slot.src_offset_));
            asm_->push(kScratchDoubleReg);
            break;
          }
          case ValueType::kS128: {
            UseScratchRegisterScope temps(asm_);
            Register scratch = temps.Acquire();
            asm_->LoadSimd128(kScratchDoubleReg,
                              liftoff::GetStackSlot(slot.src_offset_), scratch);
            asm_->lay(sp, MemOperand(sp, -kSimd128Size));
            asm_->StoreSimd128(kScratchDoubleReg, MemOperand(sp), scratch);
            break;
          }
          default:
            UNREACHABLE();
        }
        break;
      }
      case LiftoffAssembler::VarState::kRegister:
        switch (src.type().kind()) {
          case ValueType::kI64:
          case ValueType::kI32:
            asm_->push(src.reg().gp());
            break;
          case ValueType::kF32:
          case ValueType::kF64:
            asm_->push(src.reg().fp());
            break;
          case ValueType::kS128: {
            UseScratchRegisterScope temps(asm_);
            Register scratch = temps.Acquire();
            asm_->lay(sp, MemOperand(sp, -kSimd128Size));
            asm_->StoreSimd128(src.reg().fp(), MemOperand(sp), scratch);
            break;
          }
          default:
            UNREACHABLE();
        }
        break;
      case LiftoffAssembler::VarState::kIntConst: {
        DCHECK(src.type() == kWasmI32 || src.type() == kWasmI64);
        UseScratchRegisterScope temps(asm_);
        Register scratch = temps.Acquire();

        switch (src.type().kind()) {
          case ValueType::kI32:
            asm_->mov(scratch, Operand(src.i32_const()));
            break;
          case ValueType::kI64:
            asm_->mov(scratch, Operand(int64_t{slot.src_.i32_const()}));
            break;
          default:
            UNREACHABLE();
        }
        asm_->push(scratch);
        break;
      }
    }
  }
}

}  // namespace wasm
}  // namespace internal
}  // namespace v8

#undef BAILOUT

#endif  // V8_WASM_BASELINE_S390_LIFTOFF_ASSEMBLER_S390_H_
