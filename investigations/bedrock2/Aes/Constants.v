Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Word.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(**** This file defines global constants for the AES firmware, such as register
      addresses and enum values. ****)

(* Core class : defines all the constants*)
Class aes_constants T :=
  { (* Constants from autogenerated aes_regs.h *)
  AES_KEY0 : T; (* first key register address *)
  AES_IV0 : T; (* first initialization vector register address *)
  AES_DATA_IN0 : T; (* first input data register address *)
  AES_DATA_OUT0 : T; (* first output data register address *)
  AES_CTRL : T; (* control register address *)
  AES_CTRL_OPERATION : T; (* control flag position *)
  AES_CTRL_MODE_MASK : T; (* mask for control mode *)
  AES_CTRL_MODE_OFFSET : T; (* offset for control mode *)
  AES_CTRL_KEY_LEN_MASK : T; (* mask for control key length *)
  AES_CTRL_KEY_LEN_OFFSET : T; (* offset for control key length *)
  AES_CTRL_MANUAL_OPERATION :T; (* control flag position *)
  AES_STATUS : T; (* status register address *)
  AES_STATUS_IDLE : T; (* status flag position *)
  AES_STATUS_STALL : T; (* status flag position *)
  AES_STATUS_OUTPUT_VALID : T; (* status flag position *)
  AES_STATUS_INPUT_READY : T; (* status flag position *)

  (* Constants defined in aes.c *)
  AES_NUM_REGS_KEY : T; (* number of key registers *)
  AES_NUM_REGS_IV : T; (* number of initialization vector registers *)
  AES_NUM_REGS_DATA : T; (* number of in/out data registers *)

  (* Enum option definitions from aes.h *)
  kAesEnc : T; (* aes_op enum value *)
  kAesDec : T; (* aes_op enum value *)
  kAesEcb : T; (* aes_mode enum value *)
  kAesCbc : T; (* aes_mode enum value *)
  kAesCtr : T; (* aes_mode enum value *)
  kAes128 : T; (* aes_key_len enum value *)
  kAes192 : T; (* aes_key_len enum value *)
  kAes256 : T; (* aes_key_len enum value *)
  }.

(* Given the string names of all the constants, coerce them to bedrock2
   expressions with expr.var *)
Definition constant_vars
           {names : aes_constants string}
  : aes_constants expr :=
  {| AES_KEY0 := expr.var AES_KEY0;
     AES_IV0 := expr.var AES_IV0;
     AES_DATA_IN0 := expr.var AES_DATA_IN0;
     AES_DATA_OUT0 := expr.var AES_DATA_OUT0;
     AES_CTRL := expr.var AES_CTRL;
     AES_CTRL_OPERATION := expr.var AES_CTRL_OPERATION;
     AES_CTRL_MODE_MASK := expr.var AES_CTRL_MODE_MASK;
     AES_CTRL_MODE_OFFSET := expr.var AES_CTRL_MODE_OFFSET;
     AES_CTRL_KEY_LEN_MASK := expr.var AES_CTRL_KEY_LEN_MASK;
     AES_CTRL_KEY_LEN_OFFSET := expr.var AES_CTRL_KEY_LEN_OFFSET;
     AES_CTRL_MANUAL_OPERATION := expr.var AES_CTRL_MANUAL_OPERATION;
     AES_STATUS := expr.var AES_STATUS;
     AES_STATUS_IDLE := expr.var AES_STATUS_IDLE;
     AES_STATUS_STALL := expr.var AES_STATUS_STALL;
     AES_STATUS_OUTPUT_VALID := expr.var AES_STATUS_OUTPUT_VALID;
     AES_STATUS_INPUT_READY := expr.var AES_STATUS_INPUT_READY;
     AES_NUM_REGS_KEY := expr.var AES_NUM_REGS_KEY;
     AES_NUM_REGS_IV := expr.var AES_NUM_REGS_IV;
     AES_NUM_REGS_DATA := expr.var AES_NUM_REGS_DATA;
     kAesEnc := expr.var kAesEnc;
     kAesDec := expr.var kAesDec;
     kAesEcb := expr.var kAesEcb;
     kAesCbc := expr.var kAesCbc;
     kAesCtr := expr.var kAesCtr;
     kAes128 := expr.var kAes128;
     kAes192 := expr.var kAes192;
     kAes256 := expr.var kAes256;
  |}.

(* Given the Z values of all the constants, convert them to words with
   word.of_Z *)
Definition constant_words
           {width} {word : word width} {word_ok : word.ok word}
           {vals : aes_constants Z}
  : aes_constants word :=
  {| AES_KEY0 := word.of_Z AES_KEY0;
     AES_IV0 := word.of_Z AES_IV0;
     AES_DATA_IN0 := word.of_Z AES_DATA_IN0;
     AES_DATA_OUT0 := word.of_Z AES_DATA_OUT0;
     AES_CTRL := word.of_Z AES_CTRL;
     AES_CTRL_OPERATION := word.of_Z AES_CTRL_OPERATION;
     AES_CTRL_MODE_MASK := word.of_Z AES_CTRL_MODE_MASK;
     AES_CTRL_MODE_OFFSET := word.of_Z AES_CTRL_MODE_OFFSET;
     AES_CTRL_KEY_LEN_MASK := word.of_Z AES_CTRL_KEY_LEN_MASK;
     AES_CTRL_KEY_LEN_OFFSET := word.of_Z AES_CTRL_KEY_LEN_OFFSET;
     AES_CTRL_MANUAL_OPERATION := word.of_Z AES_CTRL_MANUAL_OPERATION;
     AES_STATUS := word.of_Z AES_STATUS;
     AES_STATUS_IDLE := word.of_Z AES_STATUS_IDLE;
     AES_STATUS_STALL := word.of_Z AES_STATUS_STALL;
     AES_STATUS_OUTPUT_VALID := word.of_Z AES_STATUS_OUTPUT_VALID;
     AES_STATUS_INPUT_READY := word.of_Z AES_STATUS_INPUT_READY;
     AES_NUM_REGS_KEY := word.of_Z AES_NUM_REGS_KEY;
     AES_NUM_REGS_IV := word.of_Z AES_NUM_REGS_IV;
     AES_NUM_REGS_DATA := word.of_Z AES_NUM_REGS_DATA;
     kAesEnc := word.of_Z kAesEnc;
     kAesDec := word.of_Z kAesDec;
     kAesEcb := word.of_Z kAesEcb;
     kAesCbc := word.of_Z kAesCbc;
     kAesCtr := word.of_Z kAesCtr;
     kAes128 := word.of_Z kAes128;
     kAes192 := word.of_Z kAes192;
     kAes256 := word.of_Z kAes256;
  |}.

(* This instance provide the string name for each constant *)
Definition constant_names : aes_constants string :=
  {| AES_KEY0 := "AES_KEY0(0)";
     AES_IV0 := "AES_IV0(0)";
     AES_DATA_IN0 := "AES_DATA_IN0(0)";
     AES_DATA_OUT0 := "AES_DATA_OUT0(0)";
     AES_CTRL := "AES_CTRL(0)";
     AES_CTRL_OPERATION := "AES_CTRL_OPERATION";
     AES_CTRL_MODE_MASK := "AES_CTRL_MODE_MASK";
     AES_CTRL_MODE_OFFSET := "AES_CTRL_MODE_OFFSET";
     AES_CTRL_KEY_LEN_MASK := "AES_CTRL_KEY_LEN_MASK";
     AES_CTRL_KEY_LEN_OFFSET := "AES_CTRL_KEY_LEN_OFFSET";
     AES_CTRL_MANUAL_OPERATION := "AES_CTRL_MANUAL_OPERATION";
     AES_STATUS := "AES_STATUS(0)";
     AES_STATUS_IDLE := "AES_STATUS_IDLE";
     AES_STATUS_STALL := "AES_STATUS_STALL";
     AES_STATUS_OUTPUT_VALID := "AES_STATUS_OUTPUT_VALID";
     AES_STATUS_INPUT_READY := "AES_STATUS_INPUT_READY";
     AES_NUM_REGS_KEY := "AES_NUM_REGS_KEY";
     AES_NUM_REGS_IV := "AES_NUM_REGS_IV";
     AES_NUM_REGS_DATA := "AES_NUM_REGS_DATA";
     kAesEnc := "kAesEnc";
     kAesDec := "kAesDec";
     kAesEcb := "kAesEcb";
     kAesCbc := "kAesCbc";
     kAesCtr := "kAesCtr";
     kAes128 := "kAes128";
     kAes192 := "kAes192";
     kAes256 := "kAes256";
  |}.

(* This list includes all the constants and is prepended to functions' argument
   lists to initialize their environment *)
Definition aes_globals {T} {consts : aes_constants T} : list T :=
  [ AES_KEY0
    ; AES_IV0
    ; AES_DATA_IN0
    ; AES_DATA_OUT0
    ; AES_CTRL
    ; AES_CTRL_OPERATION
    ; AES_CTRL_MODE_MASK
    ; AES_CTRL_MODE_OFFSET
    ; AES_CTRL_KEY_LEN_MASK
    ; AES_CTRL_KEY_LEN_OFFSET
    ; AES_CTRL_MANUAL_OPERATION
    ; AES_STATUS
    ; AES_STATUS_IDLE
    ; AES_STATUS_STALL
    ; AES_STATUS_OUTPUT_VALID
    ; AES_STATUS_INPUT_READY
    ; AES_NUM_REGS_KEY
    ; AES_NUM_REGS_IV
    ; AES_NUM_REGS_DATA
    ; kAesEnc
    ; kAesDec
    ; kAesEcb
    ; kAesCbc
    ; kAesCtr
    ; kAes128
    ; kAes192
    ; kAes256
  ].

(* All register addresses for the AES block *)
Definition aes_reg_addrs {width} {word : word.word width}
           {global_values : aes_constants word}
  : list word.rep :=
  AES_CTRL :: AES_STATUS ::
           (list_reg_addrs AES_KEY0 (Z.to_nat (word.unsigned AES_NUM_REGS_KEY)) 4)
           ++ (list_reg_addrs AES_IV0 (Z.to_nat (word.unsigned AES_NUM_REGS_IV)) 4)
           ++ (list_reg_addrs AES_DATA_IN0 (Z.to_nat (word.unsigned AES_NUM_REGS_DATA)) 4)
           ++ (list_reg_addrs AES_DATA_OUT0 (Z.to_nat (word.unsigned AES_NUM_REGS_DATA)) 4).

(* This class includes all the properties the AES constants must satisfy *)
Class aes_constants_ok
      {width} {word : word width} {word_ok : word.ok word}
      (global_values : aes_constants word.rep) :=
  { addrs_unique : unique_words aes_reg_addrs;
    addrs_aligned : Forall (fun addr => word.unsigned addr mod 4 = 0) aes_reg_addrs;
    addrs_small : Forall (fun addr => word.unsigned addr + 4 <= 2 ^ width) aes_reg_addrs;
    status_flags_unique_and_nonzero :
      unique_words
        ((word.of_Z 0)
           :: (map (fun flag_position => word.slu (word.of_Z 1) flag_position)
                  [AES_STATUS_IDLE
                   ; AES_STATUS_STALL
                   ; AES_STATUS_OUTPUT_VALID
                   ; AES_STATUS_INPUT_READY]));
    status_flags_inbounds :
      Forall (fun flag => word.unsigned flag < 32)
             [AES_STATUS_IDLE
              ; AES_STATUS_STALL
              ; AES_STATUS_OUTPUT_VALID
              ; AES_STATUS_INPUT_READY];

    (* control register needs to be properly formatted *)
    op_size := 1;
    mode_offset_ok :
      op_size <= word.unsigned AES_CTRL_MODE_OFFSET;
    mode_size : Z;
    key_len_offset_ok :
      word.unsigned AES_CTRL_MODE_OFFSET + mode_size
      <= word.unsigned AES_CTRL_KEY_LEN_OFFSET;
    key_len_size : Z;
    manual_operation_ok :
      word.unsigned AES_CTRL_KEY_LEN_OFFSET + key_len_size
      <= word.unsigned AES_CTRL_MANUAL_OPERATION < width;

    (* Some constants are required to have certain values *)
    nregs_key_eq : word.unsigned AES_NUM_REGS_KEY = 8;
    nregs_iv_eq : word.unsigned AES_NUM_REGS_IV = 4;
    nregs_data_eq : word.unsigned AES_NUM_REGS_DATA = 4;
    kAesEnc_eq : word.unsigned kAesEnc = 0;
    kAesDec_eq : word.unsigned kAesDec = 1;
    operation_eq : word.unsigned AES_CTRL_OPERATION = 0;
    mode_mask_eq :
      word.unsigned AES_CTRL_MODE_MASK = Z.ones mode_size;
    key_len_mask_eq :
      word.unsigned AES_CTRL_KEY_LEN_MASK = Z.ones key_len_size;

    (* Enum definitions *)
    aes_op : enum [kAesEnc; kAesDec] op_size;
    aes_mode : enum [kAesEcb; kAesCbc; kAesCtr] mode_size;
    aes_key_len : enum [kAes128; kAes192; kAes256] key_len_size;
  }.
