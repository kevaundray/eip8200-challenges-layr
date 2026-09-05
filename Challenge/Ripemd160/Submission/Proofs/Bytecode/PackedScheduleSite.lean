import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open StackRoundTemplate

private def byteLength : List Instr → Nat
  | [] => 0
  | .op _ :: rest => 1 + byteLength rest
  | .push width _ :: rest => (1 + width.val) + byteLength rest

private theorem byteLength_eq_assemble (instructions : List Instr) :
    byteLength instructions = (assembleBytes instructions).length := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;> simp [byteLength, assembleBytes_cons, ih, Nat.add_comm]

open private submissionInstructionsChunk0 submissionInstructionsChunk1
  submissionInstructionsChunk2 submissionInstructionsChunk3
  submissionInstructionsChunk4 submissionInstructionsChunk5
  submissionInstructionsChunk6 submissionInstructionsChunk7
  submissionInstructionsChunk8 submissionInstructionsChunk9
  submissionInstructionsChunk10 submissionInstructionsChunk11
  submissionInstructionsChunk12 submissionInstructionsChunk13
  submissionInstructionsChunk14 submissionInstructionsChunk15
  submissionInstructionsChunk16
  submissionInstructionsChunk0_length submissionInstructionsChunk1_length
  submissionInstructionsChunk2_length submissionInstructionsChunk3_length
  submissionInstructionsChunk4_length submissionInstructionsChunk5_length
  submissionInstructionsChunk6_length submissionInstructionsChunk7_length
  submissionInstructionsChunk8_length submissionInstructionsChunk9_length
  submissionInstructionsChunk10_length submissionInstructionsChunk11_length
  submissionInstructionsChunk12_length submissionInstructionsChunk13_length
  submissionInstructionsChunk14_length submissionInstructionsChunk15_length
  submissionInstructionsChunk16_length
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

private theorem advances_straight {instruction : Instr}
    (h : StraightLine instruction) : DenseScheduleLift.Advances instruction := by
  exact Or.inl (Or.inl h)

private theorem advances_jumpdest :
    DenseScheduleLift.Advances (.op .JUMPDEST) := by
  exact Or.inl (Or.inr (Or.inr rfl))

private theorem advances_mstore :
    DenseScheduleLift.Advances (.op .MSTORE) := by
  exact Or.inr rfl

private theorem initialTemplate_advances :
    ∀ instruction ∈ DenseScheduleTemplate.initialTemplate,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [DenseScheduleTemplate.initialTemplate, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact advances_jumpdest
  all_goals exact advances_straight (by constructor)

private theorem endianStage_advances (shift : Nat) (mask : UInt256) :
    ∀ instruction ∈ DenseScheduleTemplate.endianStage shift mask,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [DenseScheduleTemplate.endianStage, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact advances_straight (by constructor)

private theorem denseStore_advances (half : Nat) :
    ∀ instruction ∈
      [DenseScheduleTemplate.push2
          (UInt256.ofNat (DenseScheduleTemplate.denseStoreAddress half)),
        DenseScheduleTemplate.op .MSTORE],
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact advances_straight (by constructor)
  · exact advances_mstore

private theorem denseHalfTemplate_advances (half : Nat) :
    ∀ instruction ∈ DenseScheduleTemplate.denseHalfTemplate half,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [DenseScheduleTemplate.denseHalfTemplate, List.mem_append] at hmem
  rcases hmem with (h8 | h16) | hstore
  · exact endianStage_advances 8 DenseScheduleTemplate.mask8 instruction h8
  · exact endianStage_advances 16 DenseScheduleTemplate.mask16 instruction h16
  · exact denseStore_advances half instruction hstore

private theorem denseBeforeJumpTemplate_advances :
    ∀ instruction ∈ DenseScheduleTemplate.denseBeforeJumpTemplate,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [DenseScheduleTemplate.denseBeforeJumpTemplate, List.mem_append] at hmem
  rcases hmem with (hinitial | h1) | h0
  · exact initialTemplate_advances instruction hinitial
  · exact denseHalfTemplate_advances 1 instruction h1
  · exact denseHalfTemplate_advances 0 instruction h0

private def packedSchedulePrefix : List Instr :=
  submissionInstructionsChunk0 ++ submissionInstructionsChunk1 ++
    submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++
    submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++
    submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++
    submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++
    submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++
    submissionInstructionsChunk12 ++ []

private theorem packedSchedulePrefix_length : packedSchedulePrefix.length = 2600 := by
  simp [packedSchedulePrefix]

private def packedScheduleBefore : List Instr :=
  packedSchedulePrefix ++ submissionInstructionsChunk13.take 86

private theorem packedScheduleBefore_length : packedScheduleBefore.length = 2686 := by
  simp [packedScheduleBefore, packedSchedulePrefix_length]

private def packedScheduleAfter : List Instr :=
  submissionInstructionsChunk13.drop 142 ++ submissionInstructionsChunk14 ++
    submissionInstructionsChunk15 ++ submissionInstructionsChunk16

private theorem artifact_prefix_split :
    Artifact.submissionArtifact.instructions =
      packedSchedulePrefix ++
        (submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++
          submissionInstructionsChunk15 ++ submissionInstructionsChunk16) := by
  change Artifact.submissionInstructions =
    packedSchedulePrefix ++
      (submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++
        submissionInstructionsChunk15 ++ submissionInstructionsChunk16)
  simp only [Artifact.submissionInstructions, packedSchedulePrefix, List.append_assoc,
    List.nil_append]

private theorem artifact_tail_split :
    submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++
        submissionInstructionsChunk15 ++ submissionInstructionsChunk16 =
      submissionInstructionsChunk13.take 86 ++
        DenseScheduleTemplate.denseFullTemplate ++ packedScheduleAfter := by
  rfl

private theorem artifact_dense_split :
    Artifact.submissionArtifact.instructions =
      packedScheduleBefore ++ DenseScheduleTemplate.denseFullTemplate ++
        packedScheduleAfter := by
  rw [artifact_prefix_split, artifact_tail_split]
  simp [packedScheduleBefore, List.append_assoc]

private theorem artifact_dense_split_prejump :
    Artifact.submissionArtifact.instructions =
      packedScheduleBefore ++ DenseScheduleTemplate.denseBeforeJumpTemplate ++
        (DenseScheduleTemplate.finalJumpTemplate ++ packedScheduleAfter) := by
  simpa [DenseScheduleTemplate.denseFullTemplate, List.append_assoc] using
    artifact_dense_split

private theorem instructionPC_prefix_plus_segment
    (p : ProgramArtifact) (before segment : List Instr)
    (hsplit : p.instructions = before ++ segment) :
    p.instructionPC before.length + byteLength segment = p.code.size := by
  have hassembly : (assembleBytes p.instructions).length = p.code.size := by
    have h := congrArg ByteArray.size p.assembly_eq
    change (assembleBytes p.instructions).toArray.size = p.code.size at h
    simpa only [List.size_toArray] using h
  have htake : (before ++ segment).take before.length = before := by
    simp
  unfold ProgramArtifact.instructionPC
  rw [hsplit, htake, byteLength_eq_assemble]
  rw [hsplit, assembleBytes_append] at hassembly
  simpa only [List.length_append] using hassembly

private theorem instructionPC_segment_byteLength
    (p : ProgramArtifact) (before segment after : List Instr)
    (hsplit : p.instructions = before ++ segment ++ after)
    (i : Nat) (hi : i ≤ segment.length) :
    p.instructionPC (before.length + i) =
      p.instructionPC before.length + byteLength (segment.take i) := by
  have hzero := ArtifactSegment.instructionPC_segment p before segment after hsplit 0
    (by omega : 0 ≤ segment.length)
  have hzero' : p.instructionPC before.length = (assembleBytes before).length := by
    simpa using hzero
  have hi' := ArtifactSegment.instructionPC_segment p before segment after hsplit i hi
  rw [byteLength_eq_assemble, hzero']
  exact hi'

private theorem packedSchedule_slice :
    (Artifact.submissionArtifact.instructions.drop 2686).take
        DenseScheduleTemplate.denseBeforeJumpTemplate.length =
      DenseScheduleTemplate.denseBeforeJumpTemplate := by
  rfl

def packedScheduleSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      DenseScheduleTemplate.denseBeforeJumpTemplate :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    DenseScheduleTemplate.denseBeforeJumpTemplate 2686
    packedSchedule_slice
    (by
      change 2686 + DenseScheduleTemplate.denseBeforeJumpTemplate.length ≤
        Artifact.submissionInstructions.length
      rw [DenseScheduleTemplate.denseBeforeJumpTemplate_length,
        Artifact.referenceInstructions_count]
      decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := DenseScheduleTemplate.denseBeforeJumpTemplate) (by decide))
    (by decide)

private theorem denseScheduleTemplate_byteLength :
    byteLength DenseScheduleTemplate.denseBeforeJumpTemplate = 324 := by
  rw [byteLength_eq_assemble]
  exact DenseScheduleTemplate.denseBeforeJumpTemplate_byteLength

private theorem packedSchedule_start_instructionPC :
    Artifact.submissionArtifact.instructionPC 2686 = 0x109f := by
  have h := instructionPC_prefix_plus_segment Artifact.submissionArtifact
    packedScheduleBefore (DenseScheduleTemplate.denseFullTemplate ++ packedScheduleAfter)
    (by simpa only [List.append_assoc] using artifact_dense_split)
  have hlength : byteLength
      (DenseScheduleTemplate.denseFullTemplate ++ packedScheduleAfter) = 1044 := by
    decide
  rw [packedScheduleBefore_length, hlength] at h
  have hsize : Artifact.submissionArtifact.code.size = 5299 := by
    change Challenge.Ripemd160.submissionBytecode.size = 5299
    exact Challenge.Ripemd160.referenceBytecode_size
  rw [hsize] at h
  omega

private theorem packedSchedule_end_instructionPC :
    Artifact.submissionArtifact.instructionPC 2741 = 0x11e3 := by
  have h := instructionPC_segment_byteLength Artifact.submissionArtifact
    packedScheduleBefore DenseScheduleTemplate.denseBeforeJumpTemplate
    (DenseScheduleTemplate.finalJumpTemplate ++ packedScheduleAfter)
    artifact_dense_split_prejump 55
    (by decide)
  have htake :
      DenseScheduleTemplate.denseBeforeJumpTemplate.take 55 =
        DenseScheduleTemplate.denseBeforeJumpTemplate := by
    apply List.take_of_length_le
    rw [DenseScheduleTemplate.denseBeforeJumpTemplate_length]
  rw [packedScheduleBefore_length, htake, denseScheduleTemplate_byteLength,
    packedSchedule_start_instructionPC] at h
  norm_num at h
  exact h

@[simp] theorem packedScheduleSite_startPC :
    packedScheduleSite.startPC = UInt256.ofNat 0x109f := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2686) =
    UInt256.ofNat 0x109f
  rw [packedSchedule_start_instructionPC]

@[simp] theorem packedScheduleSite_endPC :
    packedScheduleSite.endPC = UInt256.ofNat 0x11e3 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2741) =
    UInt256.ofNat 0x11e3
  rw [packedSchedule_end_instructionPC]

theorem packedScheduleSite_end_eq_pcAfter :
    packedScheduleSite.endPC =
      StackRoundTrace.pcAfter packedScheduleSite.startPC
        DenseScheduleTemplate.denseBeforeJumpTemplate := by
  have h := StackRoundTrace.endPC_eq_pcAfter_sites packedScheduleSite.sites
    packedScheduleSite.startPC packedScheduleSite.endPC packedScheduleSite.head_eq
    packedScheduleSite.end_eq packedScheduleSite.contiguous
  rwa [packedScheduleSite.instruction_eq] at h

private theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (Artifact.submissionArtifact.instructionPC index)).toNat =
      Artifact.submissionArtifact.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hle := Artifact.submissionArtifact.instructionPC_le_code_size index
  have hcode := QuadLayout.code_bound
  exact Nat.lt_of_le_of_lt hle hcode

def packedScheduleFinalJump :
    LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := 2741
      instruction := .op .JUMP
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2741)
  pc_eq := pc_toNat_instructionPC 2741

def packedScheduleFinalJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [packedScheduleFinalJump.located]

private theorem runLocatedBlock_singleton
    {artifact : ProgramArtifact} {fork : Fork}
    (located : Challenge.EvmProof.Stepper.Located artifact fork) (s : State) :
    Challenge.EvmProof.Stepper.runLocatedBlock [located] s =
      Challenge.EvmProof.Stepper.runLocated located s := by
  cases h : Challenge.EvmProof.Stepper.runLocated located s with
  | none => simp [Challenge.EvmProof.Stepper.runLocatedBlock, h]
  | some t => simp [Challenge.EvmProof.Stepper.runLocatedBlock, h]

@[simp] theorem packedScheduleFinalJump_pc :
    packedScheduleFinalJump.pc = UInt256.ofNat 0x11e3 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2741) =
    UInt256.ofNat 0x11e3
  rw [packedSchedule_end_instructionPC]

theorem packedScheduleFinalJump_site_end :
    packedScheduleFinalJump.pc = packedScheduleSite.endPC := by
  calc
    packedScheduleFinalJump.pc = UInt256.ofNat 0x11e3 := packedScheduleFinalJump_pc
    _ = packedScheduleSite.endPC := packedScheduleSite_endPC.symm

theorem packedScheduleFinalJump_pc_eq_expected
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256) :
    packedScheduleFinalJump.pc =
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).pc := by
  calc
    packedScheduleFinalJump.pc = packedScheduleSite.endPC :=
      packedScheduleFinalJump_site_end
    _ = StackRoundTrace.pcAfter packedScheduleSite.startPC
        DenseScheduleTemplate.denseBeforeJumpTemplate :=
      packedScheduleSite_end_eq_pcAfter
    _ = (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).pc := by rfl

theorem runPackedScheduleFinalJump
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1023)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code returnPC.toNat = true) :
    Stepper.runLocatedBlock packedScheduleFinalJumpPath
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest) =
      some (Schedule.scheduleReturned
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest) returnPC rest) := by
  have hvalid' :
      Decode.isValidJumpDest
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.code returnPC.toNat = true := by
    simpa [DenseScheduleTemplate.denseExpectedState] using hvalid
  have h := SharedCallTrace.runLocated_jump packedScheduleFinalJump (by rfl)
    (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
      messageOffset returnPC rest) returnPC rest hstack hvalid'
  have hstate :
      { DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest with
        pc := packedScheduleFinalJump.pc
        stack := returnPC :: rest } =
        DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest := by
    rw [packedScheduleFinalJump_pc_eq_expected s messageOffset returnPC rest]
    rfl
  rw [hstate] at h
  have hsingleton :
      Stepper.runLocatedBlock packedScheduleFinalJumpPath
          (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) =
        Stepper.runLocated packedScheduleFinalJump.located
          (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) := by
    exact runLocatedBlock_singleton _ _
  have hblock :
      Stepper.runLocatedBlock packedScheduleFinalJumpPath
          (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) =
        some { DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest with
          pc := returnPC
          stack := rest } := by
    calc
      Stepper.runLocatedBlock packedScheduleFinalJumpPath
          (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) =
          Stepper.runLocated packedScheduleFinalJump.located
            (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
              messageOffset returnPC rest) := hsingleton
      _ = some { DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest with
          pc := returnPC
          stack := rest } := h
  exact hblock

def gasSteps_packedSchedule_of_raw
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hresult :
      StackRoundTrace.runInstrSeq DenseScheduleTemplate.denseBeforeJumpTemplate
        (DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
          messageOffset returnPC rest) =
      some (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest)) :
    GasSteps
      (DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
        messageOffset returnPC rest)
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest) := by
  apply DenseScheduleLift.gasSteps_of_raw packedScheduleSite
    (s := DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
      messageOffset returnPC rest)
    (t := DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
      messageOffset returnPC rest)
  · simpa [DenseScheduleTemplate.scheduleEntry] using hcode
  · simpa [DenseScheduleTemplate.scheduleEntry, State.fork] using hfork
  · simpa [DenseScheduleTemplate.scheduleEntry] using hrun
  · simpa [DenseScheduleTemplate.scheduleEntry] using hnp
  · rfl
  · exact denseBeforeJumpTemplate_advances
  · exact hresult

def gasSteps_packedSchedule_finalJump
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hstack : rest.length < 1023)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code returnPC.toNat = true) :
    GasSteps
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest)
      (Schedule.scheduleReturned
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest) returnPC rest) := by
  have hqcode :
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).executionEnv.code =
        Artifact.submissionArtifact.code := by
    simpa [DenseScheduleTemplate.denseExpectedState] using hcode
  have hqfork :
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).fork = .Osaka := by
    simpa [DenseScheduleTemplate.denseExpectedState, State.fork] using hfork
  have hqrun :
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).halt = .Running := by
    simpa [DenseScheduleTemplate.denseExpectedState] using hrun
  have hqnp :
      Precompile.isPrecompileWithConfig
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.precompileConfig
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.fork
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.codeAddr = false := by
    simpa [DenseScheduleTemplate.denseExpectedState] using hnp
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    packedScheduleFinalJumpPath
  · exact hqcode
  · exact hqfork
  · exact runPackedScheduleFinalJump s messageOffset returnPC rest hstack hvalid
  · exact hqrun
  · exact hqnp

def gasSteps_packedSchedule
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hstack : rest.length < 1023)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code returnPC.toNat = true)
    (hresult :
      StackRoundTrace.runInstrSeq DenseScheduleTemplate.denseBeforeJumpTemplate
        (DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
          messageOffset returnPC rest) =
      some (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest)) :
    GasSteps
      (DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
        messageOffset returnPC rest)
      (Schedule.scheduleReturned
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest) returnPC rest) := by
  exact (gasSteps_packedSchedule_of_raw s messageOffset returnPC rest hcode hfork hrun hnp
    hresult).trans
    (gasSteps_packedSchedule_finalJump s messageOffset returnPC rest hcode hfork hrun hnp
      hstack hvalid)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite
