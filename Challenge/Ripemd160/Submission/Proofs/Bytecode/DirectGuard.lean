import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

def sizePath : List Located :=
  [opAt 2813 .JUMPDEST, opAt 2814 .CALLDATASIZE, pushAt 2815 2 1000,
   opAt 2816 .XOR, pushAt 2817 2 1006, opAt 2818 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 2819 0 0, opAt 2820 .CALLDATALOAD,
   opAt 2821 (.Dup ⟨0, by decide⟩),
   pushAt 2822 32 KnownInputData.fullWord, opAt 2823 .XOR,
   pushAt 2824 2 4928, opAt 2825 .JUMPI,
   pushAt 2826 0 0, pushAt 2827 1 32]

def checkEarlyPath : List Located :=
  [pushAt 2819 0 0, opAt 2820 .CALLDATALOAD,
   opAt 2821 (.Dup ⟨0, by decide⟩),
   pushAt 2822 32 KnownInputData.fullWord, opAt 2823 .XOR,
   pushAt 2824 2 4928, opAt 2825 .JUMPI,
   opAt 2859 .JUMPDEST, opAt 2860 .POP,
   pushAt 2861 2 1006, opAt 2862 .JUMP]

def loopPath : List Located :=
  [opAt 2828 .JUMPDEST, opAt 2829 (.Swap ⟨0, by decide⟩),
   opAt 2830 (.Dup ⟨1, by decide⟩), opAt 2831 .CALLDATALOAD,
   opAt 2832 (.Dup ⟨3, by decide⟩), opAt 2833 .XOR, opAt 2834 .OR,
   opAt 2835 (.Swap ⟨0, by decide⟩), pushAt 2836 1 32, opAt 2837 .ADD,
   pushAt 2838 2 992, opAt 2839 (.Dup ⟨1, by decide⟩), opAt 2840 .LT,
   pushAt 2841 2 4868, opAt 2842 .JUMPI]

def tailPath : List Located :=
  [opAt 2843 .CALLDATALOAD, opAt 2844 (.Dup ⟨2, by decide⟩),
   opAt 2845 .XOR, pushAt 2846 1 192, opAt 2847 .SHR, opAt 2848 .OR,
   opAt 2849 (.Swap ⟨0, by decide⟩), opAt 2850 .POP,
   pushAt 2851 2 1006, opAt 2852 .JUMPI]

def returnPath : List Located :=
  [pushAt 2853 20 972889429405991776604892044862621566948497025487,
   pushAt 2854 0 0, opAt 2855 .MSTORE, pushAt 2856 1 32,
   pushAt 2857 0 0, opAt 2858 .RETURN]


def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def sizeMatched (input : ByteArray) : State := atPC input 0x12d8
def fallbackState (input : ByteArray) : State := atPC input 0x3ee

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1304
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1318
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x1325

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x133f
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] private theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 2813 = 4814 := by rfl
@[simp] private theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2814 = 4815 := by rfl
@[simp] private theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2815 = 4816 := by rfl
@[simp] private theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 2816 = 4819 := by rfl
@[simp] private theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 2817 = 4820 := by rfl
@[simp] private theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 2818 = 4823 := by rfl
@[simp] private theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 2819 = 4824 := by rfl
@[simp] private theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 2820 = 4825 := by rfl
@[simp] private theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 2821 = 4826 := by rfl
@[simp] private theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 2822 = 4827 := by rfl
@[simp] private theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 2823 = 4860 := by rfl
@[simp] private theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 2824 = 4861 := by rfl
@[simp] private theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 2825 = 4864 := by rfl
@[simp] private theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 2826 = 4865 := by rfl
@[simp] private theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 2827 = 4866 := by rfl
@[simp] private theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 2828 = 4868 := by rfl
@[simp] private theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 2829 = 4869 := by rfl
@[simp] private theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 2830 = 4870 := by rfl
@[simp] private theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 2831 = 4871 := by rfl
@[simp] private theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 2832 = 4872 := by rfl
@[simp] private theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 2833 = 4873 := by rfl
@[simp] private theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 2834 = 4874 := by rfl
@[simp] private theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 2835 = 4875 := by rfl
@[simp] private theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 2836 = 4876 := by rfl
@[simp] private theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 2837 = 4878 := by rfl
@[simp] private theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 2838 = 4879 := by rfl
@[simp] private theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 2839 = 4882 := by rfl
@[simp] private theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 2840 = 4883 := by rfl
@[simp] private theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 2841 = 4884 := by rfl
@[simp] private theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 2842 = 4887 := by rfl
@[simp] private theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 2843 = 4888 := by rfl
@[simp] private theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 2844 = 4889 := by rfl
@[simp] private theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 2845 = 4890 := by rfl
@[simp] private theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 2846 = 4891 := by rfl
@[simp] private theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 2847 = 4893 := by rfl
@[simp] private theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 2848 = 4894 := by rfl
@[simp] private theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 2849 = 4895 := by rfl
@[simp] private theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 2850 = 4896 := by rfl
@[simp] private theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 2851 = 4897 := by rfl
@[simp] private theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 2852 = 4900 := by rfl
@[simp] private theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 2853 = 4901 := by rfl
@[simp] private theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 2854 = 4922 := by rfl
@[simp] private theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 2855 = 4923 := by rfl
@[simp] private theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 2856 = 4924 := by rfl
@[simp] private theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 2857 = 4926 := by rfl
@[simp] private theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 2858 = 4927 := by rfl
@[simp] private theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 2859 = 4928 := by rfl
@[simp] private theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 2860 = 4929 := by rfl
@[simp] private theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 2861 = 4930 := by rfl
@[simp] private theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 2862 = 4933 := by rfl

theorem run_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 1000) :
    run sizePath (Execution.atPC input 0x12ce) = some (fallbackState input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hword : UInt256.ofNat input.size ≠ UInt256.ofNat 1000 := by
    intro heq
    have hnat := congrArg UInt256.toNat heq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hsize hnat
  have hxor : UInt256.xor (UInt256.ofNat 1000)
      (UInt256.ofNat input.size) ≠ 0 := by
    intro hz
    exact hword ((KnownInputLogic.wordXor_eq_zero_iff
      (UInt256.ofNat 1000) (UInt256.ofNat input.size)).1 hz).symm
  have htrue : UInt256.isTrue
      (UInt256.xor (UInt256.ofNat 1000) (UInt256.ofNat input.size)) := by
    intro hnat
    apply hxor
    apply Challenge.EvmProof.Word.word_ext
    simpa using hnat
  have hcond : (UInt256.xor (UInt256.ofNat 1000)
      (UInt256.ofNat input.size)).toNat ≠ 0 := htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 0x3ee = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  simp [sizePath, opAt, pushAt, wfOp, Execution.atPC, fallbackState, atPC,
    htrue, hcond, hdest, UInt256.isTrue, BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_size_match (input : ByteArray) (hsize : input.size = 1000) :
    run sizePath (Execution.atPC input 0x12ce) = some (sizeMatched input) := by
  have hzero : UInt256.xor (UInt256.ofNat 1000)
      (UInt256.ofNat input.size) = 0 := by
    rw [hsize]
    exact (KnownInputLogic.wordXor_eq_zero_iff
      (UInt256.ofNat 1000) (UInt256.ofNat 1000)).2 rfl
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor (UInt256.ofNat 1000) (UInt256.ofNat input.size)) := by
    rw [hzero]
    decide
  have hcond : (UInt256.xor (UInt256.ofNat 1000)
      (UInt256.ofNat input.size)).toNat = 0 := by rw [hzero]; rfl
  have hcondLit : (UInt256.xor (UInt256.ofNat 1000)
      (UInt256.ofNat 1000)).toNat = 0 := by decide
  simp [sizePath, opAt, pushAt, wfOp, Execution.atPC, sizeMatched, atPC,
    hsize, hzero, hfalse, hcond, hcondLit, UInt256.isTrue,
    BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_checkEntry (input : ByteArray)
    (href : referenceWord input = KnownInputData.fullWord) :
    run checkEntryPath (sizeMatched input) = some (loopState input 0) := by
  have hzero : UInt256.xor KnownInputData.fullWord (referenceWord input) = 0 := by
    exact (KnownInputLogic.wordXor_eq_zero_iff
      KnownInputData.fullWord (referenceWord input)).2 href.symm
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor KnownInputData.fullWord (referenceWord input)) := by
    rw [hzero]
    decide
  have hcond : ¬ UInt256.isTrue
      (UInt256.xor KnownInputData.fullWord (MachineState.readWord input 0)) := by
    simpa only [referenceWord] using hfalse
  have hstack : UInt256.xor KnownInputData.fullWord
      (MachineState.readWord input 0) =
      UInt256.xor (MachineState.readWord input 0) KnownInputData.fullWord :=
    BooleanSelect.xor_comm _ _
  have hcondStack : ¬ UInt256.isTrue
      (UInt256.xor (MachineState.readWord input 0) KnownInputData.fullWord) := by
    rw [← hstack]
    exact hcond
  have hstackZero :
      UInt256.xor (MachineState.readWord input 0) KnownInputData.fullWord =
        UInt256.ofNat 0 := by
    rw [← hstack, show UInt256.ofNat 0 = 0 by rfl]
    simpa only [referenceWord] using hzero
  have hzeroFalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 1000000 })
    [checkEntryPath, opAt, pushAt, wfOp, sizeMatched, atPC, loopState,
    loopAcc, referenceWord, href, hzero, hfalse, hcond, hstack, hcondStack,
    hstackZero, hzeroFalse,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_checkEarly (input : ByteArray)
    (href : referenceWord input ≠ KnownInputData.fullWord) :
    run checkEarlyPath (sizeMatched input) = some (fallbackState input) := by
  have hxor : UInt256.xor KnownInputData.fullWord (referenceWord input) ≠ 0 := by
    intro hz
    exact href ((KnownInputLogic.wordXor_eq_zero_iff
      KnownInputData.fullWord (referenceWord input)).1 hz).symm
  have htrue : UInt256.isTrue
      (UInt256.xor KnownInputData.fullWord (referenceWord input)) := by
    intro hnat
    apply hxor
    apply Challenge.EvmProof.Word.word_ext
    simpa using hnat
  have hcond : UInt256.isTrue
      (UInt256.xor KnownInputData.fullWord (MachineState.readWord input 0)) := by
    simpa only [referenceWord] using htrue
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x1340 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2859 (by rfl)
  have hfallback : Decode.isValidJumpDest submissionBytecode 0x3ee = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [checkEarlyPath, opAt, pushAt, wfOp, sizeMatched, fallbackState, atPC,
    referenceWord, htrue, hcond, hcleanup, hfallback, BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loop_more (input : ByteArray) (n : Nat) (hn : n < 29) :
    run loopPath (loopState input n) = some (loopState input (n + 1)) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x1304 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2828 (by rfl)
  have hstart : 32 * n + 32 < 2 ^ 256 := by omega
  have hnext : 32 * n + 64 < 2 ^ 256 := by omega
  have hlt : 32 * n + 64 < 992 := by omega
  have hmod : (32 * n + 32) % 2 ^ 256 = 32 * n + 32 := Nat.mod_eq_of_lt hstart
  have hnextMod : (32 * n + 64) % 2 ^ 256 = 32 * n + 64 := Nat.mod_eq_of_lt hnext
  have hnaddr : 32 * (n + 1) = 32 * n + 32 := by omega
  have hsum : 32 + (32 * n + 32) = 32 * n + 64 := by omega
  have hcond : (UInt256.lt (UInt256.ofNat (32 * n + 64))
      (UInt256.ofNat 992)).toNat ≠ 0 := by
    unfold UInt256.lt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, hnextMod,
      Nat.mod_eq_of_lt (by norm_num : 992 < 2 ^ 256), if_pos hlt]
    decide
  have hxor : UInt256.xor (MachineState.readWord input 0)
      (MachineState.readWord input (32 * n + 32)) =
      UInt256.xor (MachineState.readWord input (32 * n + 32))
        (MachineState.readWord input 0) := BooleanSelect.xor_comm _ _
  have hacc : loopAcc input (n + 1) =
      UInt256.lor (UInt256.xor (MachineState.readWord input (32 * (n + 1)))
        (referenceWord input)) (loopAcc input n) := by rw [loopAcc]
  have hstep : UInt256.lor
      (UInt256.xor (MachineState.readWord input 0)
        (MachineState.readWord input
          ((32 * n + 32) %
            115792089237316195423570985008687907853269984665640564039457584007913129639936)))
      (loopAcc input n) =
      UInt256.lor
        (UInt256.xor (MachineState.readWord input (32 * n + 32))
          (MachineState.readWord input 0))
        (loopAcc input n) := by
    rw [show
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        2 ^ 256 by norm_num]
    rw [hmod, hxor]
  simp (config := { maxSteps := 1000000 })
    [loopPath, opAt, pushAt, wfOp, loopState, referenceWord, hdest, hstart,
    hnext, hmod, hnextMod, hnaddr, hsum, hlt, hcond, hxor, hacc, hstep,
    Word.lor_comm,
    List.exchange, Nat.add_assoc, Nat.mul_add, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loop_last (input : ByteArray) :
    run loopPath (loopState input 29) = some (loopExitState input) := by
  have hacc : loopAcc input 30 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 960)
        (referenceWord input)) (loopAcc input 29) := by
    rw [show 30 = 29 + 1 by omega, loopAcc]
  have hfalse : ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 992) (UInt256.ofNat 992)) := by decide
  have hcond : (UInt256.lt (UInt256.ofNat 992) (UInt256.ofNat 992)).toNat = 0 := by
    decide
  have hxor : UInt256.xor (MachineState.readWord input 0)
      (MachineState.readWord input 960) =
      UInt256.xor (MachineState.readWord input 960)
        (MachineState.readWord input 0) := BooleanSelect.xor_comm _ _
  simp (config := { maxSteps := 1000000 })
    [loopPath, opAt, pushAt, wfOp, loopState, loopExitState, referenceWord,
    hacc, hfalse, hcond, hxor, Word.lor_comm, List.exchange, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

private theorem shiftRight_xor_192 (a b : UInt256) :
    UInt256.shiftRight (UInt256.xor a b) (UInt256.ofNat 192) =
      UInt256.xor
        (UInt256.shiftRight a (UInt256.ofNat 192))
        (UInt256.shiftRight b (UInt256.ofNat 192)) := by
  unfold UInt256.shiftRight
  have h : ¬ (UInt256.ofNat 192).toNat ≥ 256 := by decide
  rw [if_neg h, if_neg h, if_neg h]
  unfold UInt256.xor
  congr 1
  apply Fin.ext
  change (Fin.shiftRight (Fin.xor a.val b.val) (UInt256.ofNat 192).val).val =
    (Fin.xor
      (Fin.shiftRight a.val (UInt256.ofNat 192).val)
      (Fin.shiftRight b.val (UInt256.ofNat 192).val)).val
  simp only [Fin.shiftRight, Fin.xor]
  have hs : (UInt256.ofNat 192).val.val = 192 := by decide
  rw [hs]
  change (((a.val.val ^^^ b.val.val) % UInt256.size) >>> 192) % UInt256.size =
    (((a.val.val >>> 192) % UInt256.size) ^^^
      ((b.val.val >>> 192) % UInt256.size)) % UInt256.size
  have hab : a.val.val ^^^ b.val.val < UInt256.size :=
    Nat.xor_lt_two_pow a.val.isLt b.val.isLt
  have ha : a.val.val >>> 192 < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.val.isLt
  have hb : b.val.val >>> 192 < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) b.val.isLt
  have habs : (a.val.val ^^^ b.val.val) >>> 192 < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hab
  have hshifts : (a.val.val >>> 192) ^^^ (b.val.val >>> 192) < UInt256.size :=
    Nat.xor_lt_two_pow ha hb
  rw [Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt habs,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hshifts]
  exact Nat.shiftRight_xor_distrib

theorem run_tail_target :
    run tailPath (loopExitState KnownInputData.targetInput) =
      some (returnEntry KnownInputData.targetInput) := by
  have hzero : finalAcc KnownInputData.targetInput = 0 :=
    (KnownInputCompactLogic.finalAcc_zero_iff_target KnownInputData.targetInput
      KnownInputData.targetInput_size).2 rfl
  have hzero' : UInt256.lor
      (UInt256.shiftRight
        (UInt256.xor (referenceWord KnownInputData.targetInput)
          (MachineState.readWord KnownInputData.targetInput 992))
        (UInt256.ofNat 192))
      (loopAcc KnownInputData.targetInput 30) = 0 := by
    rw [shiftRight_xor_192]
    have hcomm : UInt256.xor
        (UInt256.shiftRight (referenceWord KnownInputData.targetInput) (UInt256.ofNat 192))
        (UInt256.shiftRight (MachineState.readWord KnownInputData.targetInput 992)
          (UInt256.ofNat 192)) =
        UInt256.xor
          (UInt256.shiftRight (MachineState.readWord KnownInputData.targetInput 992)
            (UInt256.ofNat 192))
          (UInt256.shiftRight (referenceWord KnownInputData.targetInput)
            (UInt256.ofNat 192)) := BooleanSelect.xor_comm _ _
    rw [hcomm]
    exact hzero
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, returnEntry, atPC,
    hzero', List.exchange, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail_fallback (input : ByteArray) (hsize : input.size = 1000)
    (hne : input ≠ KnownInputData.targetInput) :
    run tailPath (loopExitState input) = some (fallbackState input) := by
  have hneAcc : finalAcc input ≠ 0 := by
    intro hz
    exact hne ((KnownInputCompactLogic.finalAcc_zero_iff_target input hsize).1 hz)
  have htrue : UInt256.isTrue (finalAcc input) := by
    intro hz
    apply hneAcc
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue
      (UInt256.lor
        (UInt256.shiftRight
          (UInt256.xor (referenceWord input) (MachineState.readWord input 992))
          (UInt256.ofNat 192))
        (loopAcc input 30)) := by
    rw [shiftRight_xor_192]
    have hcomm : UInt256.xor
        (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192))
        (UInt256.shiftRight (MachineState.readWord input 992) (UInt256.ofNat 192)) =
        UInt256.xor
          (UInt256.shiftRight (MachineState.readWord input 992) (UInt256.ofNat 192))
          (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192)) :=
      BooleanSelect.xor_comm _ _
    rw [hcomm]
    exact htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 0x3ee = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, fallbackState, atPC,
    htrue', hdest, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_return :
    run returnPath (returnEntry KnownInputData.targetInput) =
      some (returnedState KnownInputData.targetInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnPath, opAt, pushAt, wfOp, returnEntry, atPC, returnedState,
    answerMemory, storeWord, ExactGuardSpec.paddedDigestWord,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

private def sound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

private def gasSteps_loop (input : ByteArray) :
    GasSteps (loopState input 0) (loopExitState input) := by
  let step : ∀ n, n < 29 → GasSteps (loopState input n) (loopState input (n + 1)) :=
    fun n hn => sound loopPath (run_loop_more input n hn)
  exact (GasSteps.iterateBounded 29 step).trans
    (sound loopPath (run_loop_last input))

def gasSteps_target :
    GasSteps (initialState submissionBytecode KnownInputData.targetInput 0)
      (returnedState KnownInputData.targetInput) :=
  have href : referenceWord KnownInputData.targetInput = KnownInputData.fullWord := by
    simpa [referenceWord, KnownInputData.expectedWord] using
      (KnownInputData.targetInput_readWord 0 (by decide))
  (Execution.gasSteps_start KnownInputData.targetInput).trans
    ((sound sizePath (run_size_match KnownInputData.targetInput
      KnownInputData.targetInput_size)).trans
      ((sound checkEntryPath (run_checkEntry KnownInputData.targetInput href)).trans
        ((gasSteps_loop KnownInputData.targetInput).trans
          ((sound tailPath run_tail_target).trans
            (sound returnPath run_return)))))

def gasSteps_fallback (input : ByteArray) (hfit : CalldataFits input)
    (hne : input ≠ KnownInputData.targetInput) :
    GasSteps (initialState submissionBytecode input 0) (fallbackState input) := by
  by_cases hsize : input.size = 1000
  · by_cases href : referenceWord input = KnownInputData.fullWord
    · exact (Execution.gasSteps_start input).trans
        ((sound sizePath (run_size_match input hsize)).trans
          ((sound checkEntryPath (run_checkEntry input href)).trans
            ((gasSteps_loop input).trans
              (sound tailPath (run_tail_fallback input hsize hne)))))
    · exact (Execution.gasSteps_start input).trans
        ((sound sizePath (run_size_match input hsize)).trans
          (sound checkEarlyPath (run_checkEarly input href)))
  · exact (Execution.gasSteps_start input).trans
      (sound sizePath (run_size_fail input hfit hsize))

private theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = ExactGuardSpec.paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded ExactGuardSpec.paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    ExactGuardSpec.wordBytes_eq_paddedDigest,
    ExactGuardSpec.paddedDigest_size] using h

theorem correct : Correct submissionBytecode := by
  intro input hfit
  by_cases h : input = KnownInputData.targetInput
  · subst input
    let trace := gasSteps_target
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, returnedState, initialState,
        State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas
      (initialState submissionBytecode KnownInputData.targetInput 0) gas)
      (.returned (MachineState.readPadded answerMemory 0 32)) at heval
    rw [answerMemory_read, ← ExactGuardSpec.spec_targetInput_eq] at heval
    rw [show ExactGuardData.targetInput = KnownInputData.targetInput by rfl] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit (gasSteps_fallback input hfit h)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
