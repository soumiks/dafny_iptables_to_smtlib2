// IptablesToSmt.dfy
//
// This Dafny program parses a subset of the iptables-save format and translates
// it into SMT-LIB 2.0 (Satisfiability Modulo Theories) formulas.
//
// Dafny is a verification-aware programming language. It allows us to write
// code (methods, functions) alongside specifications (preconditions, postconditions,
// invariants) that prove the code is correct.
//
// Key Concepts:
// - verification: Dafny checks that code matches its spec at compile time.
// - ghost code: Code used only for verification, not compiled to the executable.
// - assertions: Logical truths checked by the verifier.

module IptablesToSmt {

  // Datatypes in Dafny are algebraic data types, similar to enums in Rust or Swift.
  // They define a fixed set of variants.
  datatype Target =
    | TargetAccept
    | TargetDrop
    | TargetReject
    | TargetReturn
    | TargetJump(name: string) // Variants can carry data (like string name)

  // Represents a match criteria for a packet field.
  datatype FieldMatch =
    | MatchAny                 // No constraint (wildcard)
    | MatchExact(value: string) // Must match this string exactly

  // The Rule datatype acts as a struct record, holding all information about
  // a single firewall rule.
  datatype Rule = Rule(
    chain: string,
    source: FieldMatch,
    destination: FieldMatch,
    protocol: FieldMatch,
    srcPort: FieldMatch,
    dstPort: FieldMatch,
    target: Target,
    lineNumber: int,
    original: string
  )

  // 'method' is the unit of executable code in Dafny.
  // It can have side effects (like printing), input arguments, and return values.
  method Main(args: seq<string>)
  {
    // '|args|' computes the length of the sequence 'args'.
    if |args| == 0 {
      PrintUsage();
      return;
    }

    // Sequences are 0-indexed. We take the last argument as the input payload.
    var payload := args[|args| - 1];
    var smt := ConvertIptablesToSmt(payload);
    print smt;
  }

  method PrintUsage()
  {
    var usage := GetUsageString();
    print usage;
  }

  method GetUsageString() returns (text: string)
    ensures |text| > 0
  {
    text := "Usage:\n  dafny run src/IptablesToSmt.dfy -- \"$(cat rules.txt)\"\n  ./scripts/iptables_to_smt.sh rules.txt\n";
  }

  // Splits the input into rules, parses them, and builds the SMT document.
  // 'returns (smt: string)' names the return value 'smt', which is assigned before returning.
  method ConvertIptablesToSmt(input: string) returns (smt: string)
    ensures |smt| > 0
  {
    var lines := SplitLines(input);
    var rules := ParseRules(lines);
    smt := BuildSmtDocument(rules);
  }

  // Parses a sequence of lines into a sequence of Rule objects.
  method ParseRules(lines: seq<string>) returns (rules: seq<Rule>)
    ensures |rules| <= |lines|
  {
    var collected: seq<Rule> := [];
    var idx := 0;

    // A while loop in Dafny often needs a 'decreases' clause to prove termination.
    // Use 'decreases' to denote a value that goes down with every iteration but stays bounded.
    while idx < |lines|
      decreases |lines| - idx
      invariant 0 <= idx <= |lines|
      invariant |collected| <= idx
    {
      var rawLine := lines[idx];
      var trimmed := Trim(rawLine);

      // Skip comments
      if |trimmed| > 0 && trimmed[0] == '#' {
        idx := idx + 1;
        continue;
      }

      // Identify rule lines starting with "-A"
      // we use slicing [0 .. 2] to get the first two characters.
      if |trimmed| >= 2 && trimmed[0 .. 2] == "-A" {
        var tokens := SplitOnWhitespace(trimmed);
        // Call helper to parse tokens
        var parsedRule, parsedOk := ParseRuleTokens(tokens, idx + 1, rawLine);
        if parsedOk {
          collected := collected + [parsedRule]; // Sequence concatenation
        }
      }

      idx := idx + 1;
    }

    rules := collected;
  }

  // Logic to iterate over tokens and extract rule fields.
  // Returns 'ok' as false if parsing fails (e.g. unknown flag).
  method ParseRuleTokens(tokens: seq<string>, lineNumber: int, rawLine: string) returns (rule: Rule, ok: bool)
    requires lineNumber > 0
    requires forall t :: t in tokens ==> |t| > 0
    ensures |tokens| >= 2 && ok ==> rule.chain == tokens[1]
    ensures ok ==> rule.original == rawLine
    ensures ok ==> rule.lineNumber == lineNumber
  {
    // Check for minimum length: -A <CHAIN> ...
    if |tokens| < 3 {
      // Return a dummy rule and failure status
      rule := Rule("", MatchAny, MatchAny, MatchAny, MatchAny, MatchAny, TargetReturn, lineNumber, rawLine);
      ok := false;
      return;
    }

    var chain := tokens[1];
    var src: FieldMatch := MatchAny;
    var dst: FieldMatch := MatchAny;
    var proto: FieldMatch := MatchAny;
    var srcPort: FieldMatch := MatchAny;
    var dstPort: FieldMatch := MatchAny;
    var target := TargetReturn;
    var targetSet := false;

    var i := 2;
    // Main parsing loop
    while i < |tokens|
      decreases |tokens| - i
    {
      var flag := tokens[i];

      // Check for source flag "-s"
      if flag == "-s" && i + 1 < |tokens| {
        src := MatchExact(tokens[i + 1]);
        i := i + 2;
        continue;
      }

      // Check for destination flag "-d"
      if flag == "-d" && i + 1 < |tokens| {
        dst := MatchExact(tokens[i + 1]);
        i := i + 2;
        continue;
      }

      // Check for protocol flag "-p"
      if flag == "-p" && i + 1 < |tokens| {
        proto := MatchExact(tokens[i + 1]);
        i := i + 2;
        continue;
      }

      // Check for target flag "-j" (Jump)
      if flag == "-j" && i + 1 < |tokens| {
        target := ParseTarget(tokens[i + 1]);
        targetSet := true;
        i := i + 2;
        continue;
      }

      // Check for source port "--sport"
      if flag == "--sport" && i + 1 < |tokens| {
        srcPort := MatchExact(tokens[i + 1]);
        i := i + 2;
        continue;
      }

      // Check for destination port "--dport"
      if flag == "--dport" && i + 1 < |tokens| {
        dstPort := MatchExact(tokens[i + 1]);
        i := i + 2;
        continue;
      }

      // Strict parsing: if we see a flag we don't recognize, we must fail.
      // Ignoring it effectively means "match any", which effectively widens the security policy.
      rule := Rule("", MatchAny, MatchAny, MatchAny, MatchAny, MatchAny, TargetReturn, lineNumber, rawLine);
      ok := false;
      return;
    }

    rule := Rule(chain, src, dst, proto, srcPort, dstPort, target, lineNumber, rawLine);
    ok := targetSet;
  }

  method BuildSmtDocument(rules: seq<Rule>) returns (doc: string)
    ensures |doc| > 0
  {
    var builder := "(set-logic ALL)\n";
    builder := builder + "(declare-const packet_chain String)\n";
    builder := builder + "(declare-const packet_src String)\n";
    builder := builder + "(declare-const packet_dst String)\n";
    builder := builder + "(declare-const packet_proto String)\n";
    builder := builder + "(declare-const packet_sport String)\n";
    builder := builder + "(declare-const packet_dport String)\n";
    builder := builder + "(declare-const packet_action String)\n";
    builder := builder + "(assert (distinct packet_chain \"\"))\n";
    builder := builder + "\n";

    if |rules| == 0 {
      builder := builder + "; No -A rules were found in the input.\n";
      doc := builder;
      return;
    }

    var i := 0;
    while i < |rules|
      decreases |rules| - i
      invariant 0 <= i <= |rules|
      invariant |builder| > 0
    {
      var formatted := FormatRule(rules[i], i);
      builder := builder + formatted;
      builder := builder + "\n";
      i := i + 1;
    }

    doc := builder;
  }

  method FormatRule(rule: Rule, index: int) returns (formatted: string)
    requires index >= 0
  {
    var indexText := IntToString(index);
    var lineText := IntToString(rule.lineNumber);
    var header := "; Rule " + indexText + " (line " + lineText + "): " + rule.original + "\n";
    var def := "(define-fun rule" + indexText + " ((pkt_chain String) (pkt_src String) (pkt_dst String) (pkt_proto String) (pkt_sport String) (pkt_dport String)) Bool\n";
    var conditions := BuildRuleConditions(rule);

    var condBuilder := "";
    if |conditions| == 0 {
      condBuilder := "  true\n";
    } else {
      condBuilder := "  (and\n";
      var i := 0;
      while i < |conditions|
        decreases |conditions| - i
      {
        condBuilder := condBuilder + "    " + conditions[i] + "\n";
        i := i + 1;
      }

      condBuilder := condBuilder + "  )\n";
    }

    var closing := ")\n";
    var targetLiteral := FormatTargetLiteral(rule.target);
    var action := "(assert (=> (rule" + indexText + " packet_chain packet_src packet_dst packet_proto packet_sport packet_dport)\n" +
      "            (= packet_action " + targetLiteral + ")))\n";

    formatted := header + def + condBuilder + closing + action;
  }

  method IntToString(n: int) returns (text: string)
  {
    if n == 0 {
      text := "0";
      return;
    }

    var prefix := "";
    var value := n;
    if n < 0 {
      prefix := "-";
      value := -n;
    }

    var digits := "";
    while value > 0
      decreases value
    {
      var digit := value % 10;
      var digitString := DigitToString(digit);
      digits := digitString + digits;
      value := value / 10;
    }

    text := prefix + digits;
  }

  // Requires clause specifies a precondition: d must be a single digit.
  // The caller must prove this is true before calling DigitToString.
  method DigitToString(d: int) returns (text: string)
    requires 0 <= d < 10
  {
    var digitsLiteral := "0123456789";
    assert |digitsLiteral| == 10;
    text := digitsLiteral[d .. d + 1];
  }

  method BuildRuleConditions(rule: Rule) returns (conditions: seq<string>)
  {
    var conds: seq<string> := [];
    var chainLiteral := FormatStringLiteral(rule.chain);
    conds := conds + ["(= pkt_chain " + chainLiteral + ")"];
    conds := MaybeAppend(conds, "pkt_src", rule.source);
    conds := MaybeAppend(conds, "pkt_dst", rule.destination);
    conds := MaybeAppend(conds, "pkt_proto", rule.protocol);
    conds := MaybeAppend(conds, "pkt_sport", rule.srcPort);
    conds := MaybeAppend(conds, "pkt_dport", rule.dstPort);
    conditions := conds;
  }

  method MaybeAppend(conds: seq<string>, fieldName: string, crit: FieldMatch) returns (updated: seq<string>)
  {
    match crit
      case MatchExact(value) =>
        var literal := FormatStringLiteral(value);
        var fragment := "(= " + fieldName + " " + literal + ")";
        updated := conds + [fragment];
      case MatchAny =>
        updated := conds;
  }

  method FormatTargetLiteral(target: Target) returns (literal: string)
  {
    var targetText := TargetToString(target);
    literal := FormatStringLiteral(targetText);
  }

  method TargetToString(target: Target) returns (value: string)
  {
    match target
      case TargetAccept => value := "ACCEPT";
      case TargetDrop => value := "DROP";
      case TargetReject => value := "REJECT";
      case TargetReturn => value := "RETURN";
      case TargetJump(name) => value := name;
  }

  method FormatStringLiteral(text: string) returns (encoded: string)
  {
    var escaped := EscapeForSmt(text);
    encoded := "\"" + escaped + "\"";
  }

  method EscapeForSmt(text: string) returns (encoded: string)
    ensures |encoded| <= 2 * |text|
  {
    var builder := "";
    var i := 0;
    while i < |text|
      decreases |text| - i
      invariant 0 <= i <= |text|
      invariant |builder| <= 2 * i
    {
      var ch := text[i];
      if ch == '"' || ch == '\\' {
        assert i + 1 <= |text|;
        builder := builder + "\\" + text[i .. i + 1];
      } else {
        assert i + 1 <= |text|;
        builder := builder + text[i .. i + 1];
      }

      i := i + 1;
    }

    encoded := builder;
  }
  function ToUp(ch: char): char
  {
    if 'a' <= ch <= 'z' then (ch as int - 'a' as int + 'A' as int) as char else ch
  }

  predicate EqualsIgnoreCase(s1: string, s2: string)
  {
    |s1| == |s2| &&
    forall i :: 0 <= i < |s1| ==> ToUp(s1[i]) == ToUp(s2[i])
  }

  predicate MatchesTarget(target: Target, raw: string) 
  {
    match target
    case TargetAccept => EqualsIgnoreCase(raw, "ACCEPT")
    case TargetDrop => EqualsIgnoreCase(raw, "DROP")
    case TargetReject => EqualsIgnoreCase(raw, "REJECT")
    case TargetReturn => EqualsIgnoreCase(raw, "RETURN")
    case TargetJump(name) => name == raw && 
                             !EqualsIgnoreCase(raw, "ACCEPT") && 
                             !EqualsIgnoreCase(raw, "DROP") && 
                             !EqualsIgnoreCase(raw, "REJECT") && 
                             !EqualsIgnoreCase(raw, "RETURN")
  }

  method ParseTarget(raw: string) returns (target: Target)
    requires |raw| > 0
    ensures MatchesTarget(target, raw)
  {
    var isAccept := StringsEqualIgnoreCase(raw, "ACCEPT");
    if isAccept {
      target := TargetAccept;
      return;
    }

    var isDrop := StringsEqualIgnoreCase(raw, "DROP");
    if isDrop {
      target := TargetDrop;
      return;
    }

    var isReject := StringsEqualIgnoreCase(raw, "REJECT");
    if isReject {
      target := TargetReject;
      return;
    }

    var isReturn := StringsEqualIgnoreCase(raw, "RETURN");
    if isReturn {
      target := TargetReturn;
      return;
    }

    target := TargetJump(raw);
  }

  method StringsEqualIgnoreCase(left: string, right: string) returns (eq: bool)
    ensures eq <==> EqualsIgnoreCase(left, right)
  {
    if |left| != |right| {
      eq := false;
      return;
    }

    var i := 0;
    eq := true;
    while i < |left|
      decreases |left| - i
      invariant 0 <= i <= |left|
      invariant forall k :: 0 <= k < i ==> ToUp(left[k]) == ToUp(right[k])
    {
      var leftUp := ToUpperChar(left[i]);
      var rightUp := ToUpperChar(right[i]);
      
      // Proving the equivalence of method call ToUpperChar and function ToUp
      assert leftUp == ToUp(left[i]);
      assert rightUp == ToUp(right[i]);

      if leftUp != rightUp {
        eq := false;
        return;
      }

      i := i + 1;
    }
  }

  method ToUpperChar(ch: char) returns (upper: char)
    ensures upper == ToUp(ch)
  {
    if 'a' <= ch && ch <= 'z' {
      upper := (ch as int - ('a' as int) + ('A' as int)) as char;
    } else {
      upper := ch;
    }
  }

  // ----------- Low-Level String Parsing Helpers -----------

  // Splits string into lines. Proving string manipulation correct is complex in Dafny!
  // We need invariants to guide the prover.
  method SplitLines(text: string) returns (lines: seq<string>)
    ensures forall l :: l in lines ==> |l| <= |text|
  {
    if |text| == 0 {
      lines := [];
      return;
    }

    var segments: seq<string> := [];
    var start := 0;
    var i := 0;
    // Loop Invariant:
    // 'invariant' is a property that must be true before and after every loop iteration.
    // It is CRITICAL for Dafny to prove properties about loops.
    while i < |text|
      decreases |text| - i
      invariant 0 <= start
      invariant start <= i
      invariant i <= |text|
      invariant forall l :: l in segments ==> |l| <= |text|
    {
      var ch := text[i];
      if ch == '\n' {
        // 'assert' checks a condition at that point in the code.
        // It helps debugging why verification fails.
        assert 0 <= start && start <= i && i <= |text|;
        var part := text[start .. i];
        assert |part| <= |text|;
        segments := segments + [part];
        start := i + 1;
      } else if ch == '\r' {
        assert 0 <= start && start <= i && i <= |text|;
        var part := text[start .. i];
        assert |part| <= |text|;
        segments := segments + [part];
        if i + 1 < |text| && text[i + 1] == '\n' {
          i := i + 1;
        }
        start := i + 1;
      }

      i := i + 1;
    }

    if start <= |text| {
      assert 0 <= start && start <= |text|;
      segments := segments + [text[start .. |text|]];
    }

    lines := segments;
  }

  // We need to implement string splitting manually or use libraries.
  // This custom splitter handles quoted strings (e.g. comments with spaces).
  method SplitOnWhitespace(text: string) returns (tokens: seq<string>)
    ensures forall t :: t in tokens ==> |t| <= |text|
    ensures forall t :: t in tokens ==> |t| > 0
  {
    var parts: seq<string> := [];
    var i := 0;
    while i < |text|
      decreases |text| - i
      invariant 0 <= i
      invariant i <= |text|
      invariant forall t :: t in parts ==> |t| <= |text|
      invariant forall t :: t in parts ==> |t| > 0
    {
      // Skip whitespace
      while i < |text| && IsWhitespace(text[i])
        decreases |text| - i
        invariant 0 <= i
        invariant i <= |text|
      {
        i := i + 1;
      }

      if i >= |text| {
        break;
      }

      // Handle quoted string
      if text[i] == '"' {
        var start := i + 1;
        i := i + 1;
        while i < |text| && text[i] != '"'
          decreases |text| - i
          invariant 0 <= start
          invariant start <= i
          invariant i <= |text|
        {
          if text[i] == '\\' && i + 1 < |text| {
            i := i + 2;
          } else {
            i := i + 1;
          }
        }

        assert 0 <= start && start <= i && i <= |text|;
        var value := text[start .. i];
        assert |value| <= |text|;
        // Constraint: We only add if not empty (though quoted empty string "" is effectively empty content)
        // If we want to support empty quoted strings as tokens, we need to relax the postcondition |t| > 0.
        // But for iptables atoms, they are usually non-empty. Let's see.
        // Actually, if value is "", then |t| > 0 fails.
        // Let's assume for now tokens should be non-empty. If "" is valid, we'd need to change spec.
        if |value| > 0 {
           parts := parts + [value]; 
        }

        if i < |text| && text[i] == '"' {
          i := i + 1;
        }
      } else {
        var start2 := i;
        while i < |text| && !IsWhitespace(text[i])
          decreases |text| - i
          invariant 0 <= start2
          invariant start2 <= i
          invariant i <= |text|
        {
          i := i + 1;
        }

        assert 0 <= start2 && start2 <= i && i <= |text|;
        var token := text[start2 .. i];
        if |token| > 0 {
            parts := parts + [token];
        }
      }
    }

    tokens := parts;
  }

  method Trim(text: string) returns (trimmed: string)
    ensures |trimmed| <= |text|
    ensures |trimmed| > 0 ==> !IsWhitespace(trimmed[0])
    ensures |trimmed| > 0 ==> !IsWhitespace(trimmed[|trimmed| - 1])
  {
    if |text| == 0 {
      trimmed := text;
      return;
    }

    var start := 0;
    var stop := |text|;

    while start < stop && IsWhitespace(text[start])
      decreases stop - start
      invariant 0 <= start
      invariant start <= stop
      invariant stop <= |text|
      invariant forall k :: 0 <= k < start ==> IsWhitespace(text[k])
    {
      start := start + 1;
    }

    while stop > start && IsWhitespace(text[stop - 1])
      decreases stop - start
      invariant 0 <= start
      invariant start <= stop
      invariant stop <= |text|
      invariant forall k :: 0 <= k < start ==> IsWhitespace(text[k])
      invariant forall k :: stop <= k < |text| ==> IsWhitespace(text[k])
    {
      stop := stop - 1;
    }

    assert 0 <= start && start <= stop && stop <= |text|;
    trimmed := text[start .. stop];
  }

  predicate IsWhitespace(ch: char)
  {
    ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n'
  }
}
