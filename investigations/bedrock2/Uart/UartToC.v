Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import bedrock2.ToCString.
Require Import bedrock2.Variables.
Require Import coqutil.Z.HexNotation.
Require Import Bedrock2Experiments.Uart.Uart.
Require Import Bedrock2Experiments.LibBase.Bitfield.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import Bedrock2Experiments.Uart.Constants.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Existing Instance constant_names.

(* Redefinition from bedrock2's ToCString; the only difference is that globals
   are stripped out of the arguments list in function calls *)
Fixpoint c_cmd (indent : string) (c : cmd) : string :=
  match c with
  | cmd.store s ea ev
    => indent ++ "_br2_store(" ++ c_expr ea ++ ", " ++ c_expr ev ++ ", " ++ c_size s ++ ");" ++ LF
  | cmd.stackalloc x n body =>
    indent ++ c_var x ++ " = alloca(" ++ c_lit n ++ "); // TODO untested" ++ LF ++
    c_cmd indent body
  | cmd.set x ev =>
    indent ++ c_var x ++ " = " ++ c_expr ev ++ ";" ++ LF
  | cmd.unset x =>
    indent ++ "// unset " ++ c_var x ++ LF
  | cmd.cond eb t f =>
    indent ++ "if (" ++ c_expr eb ++ ") {" ++ LF ++
      c_cmd ("  "++indent) t ++
    indent ++ "} else {" ++ LF ++
      c_cmd ("  "++indent) f ++
    indent ++ "}" ++ LF
  | cmd.while eb c =>
    indent ++ "while (" ++ c_expr eb ++ ") {" ++ LF ++
      c_cmd ("  "++indent) c ++
    indent ++ "}" ++ LF
  | cmd.seq c1 c2 =>
    c_cmd indent c1 ++
    c_cmd indent c2
  | cmd.skip =>
    indent ++ "/*skip*/" ++ LF
  | cmd.call binds f arges =>
    (* the below line filters out globals from arguments in the declaration *)
  (*let arges := filter (fun e => match e with
                               | expr.var s => negb (existsb (String.eqb s) uart_globals)
                               | _ => true
                               end) arges in
     indent ++ c_call (List.map c_var binds) (c_fun f) (List.map c_expr arges) *)
     indent ++ c_call (List.map c_var binds) (c_fun f) (List.map c_expr arges)
  | cmd.interact binds action es =>
    indent ++ c_act binds action (List.map c_expr es)
  end.

(* Redefinition to avoid -Werror=strict-prototypes. Can be removed once mit-plv/bedrock2#188 lands *)
Definition fmt_c_decl (rett : string) (args : list String.string) (name : String.string) (retptrs : list String.string) : string :=
  let argstring : String.string :=
    (match args, retptrs with
     | nil, nil => "void"
     | _, _ => concat ", " (
         List.map (fun a => "uintptr_t "++c_var a) args ++
         List.map (fun r => "uintptr_t* "++c_var r) retptrs)
     end)
  in
  (rett ++ " " ++ c_fun name ++ "(" ++ argstring ++ ")").

(* Redefinition from bedrock2's ToCString; the only difference is that globals
   are stripped out of the arguments list in function declarations *)
Definition c_func '(name, (args, rets, body)) :=
  let decl_retvar_retrenames : string * option String.string * list (String.string * String.string) :=
      (* the below line filters out globals from arguments in the declaration *)
      let args := List_minus String.eqb args uart_globals in
      match rets with
      | nil => (fmt_c_decl "void" args name nil, None, nil)
      | cons r0 _ =>
        let r0 := List.last rets r0 in
        let rets' := List.removelast rets in
        let retrenames := fst (rename_outs rets' (cmd.vars body)) in
        (fmt_c_decl "uintptr_t" args name (List.map snd retrenames), Some r0, retrenames)
      end in
  let decl := fst (fst decl_retvar_retrenames) in
  let retvar := snd (fst decl_retvar_retrenames) in
  let retrenames := snd decl_retvar_retrenames in
  let localvars : list String.string := List_uniq String.eqb (
      let allvars := (List.app (match retvar with None => nil | Some v => cons v nil end) (cmd.vars body)) in
      (List_minus String.eqb allvars args)) in
  decl ++ " {" ++ LF ++
    let indent := "  " in
    (match localvars with nil => "" | _ => indent ++ "uintptr_t " ++ concat ", " (List.map c_var localvars) ++ ";" ++ LF end) ++
    c_cmd indent body ++
    concat "" (List.map (fun '(o, optr) => indent ++ "*" ++ c_var optr ++ " = " ++ c_var o ++ ";" ++ LF) retrenames) ++
    indent ++ "return" ++ (match retvar with None => "" | Some rv => " "++c_var rv end) ++ ";" ++ LF ++
    "}" ++ LF.

Definition dquote : string := String (Ascii.ascii_of_nat 34) EmptyString.
Definition uart_c_template_top : list string :=
  [ "// Autogenerated from Coq based on LowRISC implementation"
    ; ""
    ; "// Copyright lowRISC contributors."
    ; "// Licensed under the Apache License, Version 2.0, see LICENSE for details."
    ; "// SPDX-License-Identifier: Apache-2.0"
    ; ""
    ; "#include " ++ dquote ++ "sw/device/silicon_creator/lib/drivers/uart.h" ++ dquote
    ; ""
    ; "#include " ++ dquote ++ "sw/device/lib/base/memory.h" ++ dquote ++ " // for bedrock2"

    ; ""
    ; "#include " ++ dquote ++ "sw/device/lib/arch/device.h" ++ dquote
    ; "#include " ++ dquote ++ "sw/device/lib/base/bitfield.h" ++ dquote
    ; "#include " ++ dquote ++ "sw/device/silicon_creator/lib/base/abs_mmio.h" ++ dquote
    ; "#include " ++ dquote ++ "sw/device/silicon_creator/lib/error.h" ++ dquote
    ; ""
    ; "#include " ++ dquote ++ "hw/top_earlgrey/sw/autogen/top_earlgrey.h" ++ dquote
    ; "#include " ++ dquote ++ "uart_regs.h" ++ dquote ++ "  // Generated."
    ; ""
    ; "// bedrock2 memory-access functions"
    ; "static inline uintptr_t _br2_load(uintptr_t a, size_t sz) {"
    ; "  uintptr_t r = 0;"
    ; "  r = *((volatile uintptr_t *)a);"
    ; "  //memcpy(&r, (void*)a, sz);"
    ; "  return r;"
    ; "}"
    ; ""
    ; "static inline void _br2_store(uintptr_t a, uintptr_t v, size_t sz) {"
    ; "  *((volatile uintptr_t *) a) = v;"
    ; "  //memcpy((void*)a, &v, sz);"
    ; "}"].

Definition uart_c_template_bottom : list string :=
  [  "rom_error_t uart_init(uint32_t precalculated_nco) {"
    ;"  return b2_uart_init((uintptr_t) precalculated_nco);"
    ;"}"
    ;""
    ;"void uart_putchar(uint8_t byte) {"
    ;"  b2_uart_putchar((uintptr_t) byte);"
    ;"}"
    ;""
    ;"size_t uart_write(const uint8_t *data, size_t len) {"
    ;"  return b2_uart_write((uintptr_t) data, (uintptr_t) len);"
    ;"}"
    ;""
    ;"size_t uart_sink(void *uart, const char *data, size_t len) {"
      ;"  return b2_uart_sink((uintptr_t) uart, (uintptr_t) data, (uintptr_t) len);"
    ;"}"].

Definition funcs := [
  bitfield_field32_write
  ;bitfield_field32_read
  ;bitfield_bit32_read
  ;bitfield_bit32_write
  ;abs_mmio_write32
  ;abs_mmio_read32
  ;uart_reset
  ;uart_init
  ;uart_tx_full
  ;uart_tx_idle
  ;uart_putchar
  ;uart_write
  ;uart_sink
  ].

Definition make_uart_c :=
  concat LF (uart_c_template_top
                ++ map (fun f => "static " ++ c_func f) funcs
                ++ uart_c_template_bottom).

Redirect "uart.c" Compute make_uart_c.
