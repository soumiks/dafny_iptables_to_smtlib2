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
    // Dafny's Main receives the executable name as args[0].
    // If we only have the executable name (size 1) or less, we have no input.
    if |args| <= 1 {
      PrintUsage();
      return;
    }

    // Sequences are 0-indexed. We take the last argument as the input payload.
    var payload := args[|args| - 1];
    
    // Additionally, if the payload is explicitly empty, we might want to show usage or just process it.
    // Given the user request "if there is no input, print the usage help", explicit empty string argument could be debatable,
    // but typically CLI tools treat empty string arg as empty input.
    // Let's stick to the arg count check for now as the primary fix.
    
    // Runtime check to respect the precondition we added
    if exists k :: 0 <= k < |payload| && payload[k] == '\r' {
      print "Error: Input contains carriage returns (\\r). Please normalize to \\n only.\n";
      return;
    }
    
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
    requires forall k :: 0 <= k < |input| ==> input[k] != '\r'
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
  // Helper to find a flag's value in the token sequence.
  function FindMatch(tokens: seq<string>, flag: string): FieldMatch
    requires forall t :: t in tokens ==> |t| > 0
    ensures FindMatch(tokens, flag).MatchExact? ==> |FindMatch(tokens, flag).value| > 0
  {
    if |tokens| < 2 then MatchAny
    else if tokens[0] == flag then MatchExact(tokens[1])
    else FindMatch(tokens[1..], flag)
  }


  // Helper to check if the token sequence contains only valid flags.
  // In Dafny 4, 'function' is compiled by default.
  // Helper to check if the token sequence contains only valid flags.
  // We extended this to support more iptables flags.
  function ValidTokens(tokens: seq<string>): bool
    decreases |tokens|
  {
    if |tokens| < 1 then true
    else 
      var t := tokens[0];
      // Binary flags (flag + value)
      if t == "-s" || t == "-d" || t == "-p" || 
         t == "--sport" || t == "--dport" || 
         t == "-j" || 
         t == "-i" || t == "-o" || // Interfaces
         t == "-t" || t == "-m" || // Tables and Modules
         t == "--to-destination" || t == "--to-source" || // NAT
         t == "--log-prefix" || t == "--log-level" || // Logging
         t == "--limit" || t == "--limit-burst" || // Limit
         t == "--ctstate" || // Conntrack
         t == "--seconds" || t == "--hitcount" || t == "--name" || // Recent
         t == "--dports" || t == "--sports" // Multiport
      then
         if |tokens| >= 2 then ValidTokens(tokens[2..]) else false
      
      // Nullary flags (flag only)
      else if t == "--set" || t == "--update" || t == "--rcheck" || t == "--remove" || // Recent
              t == "--rsource" || t == "--rdest" 
      then
         ValidTokens(tokens[1..])
         
      // -A is special (usually start of rule, but might appear if tokens passed weirdly? 
      // In ParseRules, -A is consumed before calling this. But if it appears inside? 
      // Strictly -A should be at start. Let's keep it as binary if it appears here.)
      else if t == "-A" then 
         if |tokens| >= 2 then ValidTokens(tokens[2..]) else false   
      else
         // Unknown token/flag
         // To be robust for strict verification, we reject unknown flags.
         false 
  }
  
  // Note: The original ParseRuleTokens logic was slightly more permissive/different about where flags appear.
  // But strictly, flags should be essentially recursive.
  // However, ParseRuleTokens skips the first 2 tokens (-A CHAIN).
  // So we will just look for flags in tokens[2..].

  method ParseRuleTokens(tokens: seq<string>, lineNumber: int, rawLine: string) returns (rule: Rule, ok: bool)
    requires lineNumber > 0
    requires forall t :: t in tokens ==> |t| > 0
    ensures |tokens| >= 3 && ok ==> rule.chain == tokens[1]
    ensures ok ==> rule.original == rawLine
    ensures ok ==> rule.lineNumber == lineNumber
    // Strong Specs:
    ensures ok ==> |tokens| >= 3 
    ensures ok ==> (rule.source == FindMatch(tokens[2..], "-s"))
    ensures ok ==> (rule.destination == FindMatch(tokens[2..], "-d"))
    ensures ok ==> (rule.protocol == FindMatch(tokens[2..], "-p"))
    ensures ok ==> (rule.srcPort == FindMatch(tokens[2..], "--sport"))
    ensures ok ==> (rule.dstPort == FindMatch(tokens[2..], "--dport"))
    // Guarded implication:
    ensures (|tokens| >= 3 && ValidTokens(tokens[2..]) && FindMatch(tokens[2..], "-j").MatchExact?) ==> ok
  {
    // Check for minimum length: -A <CHAIN> ...
    if |tokens| < 3 {
      rule := Rule("", MatchAny, MatchAny, MatchAny, MatchAny, MatchAny, TargetReturn, lineNumber, rawLine);
      ok := false;
      return;
    }

    var chain := tokens[1];
    var rest := tokens[2..];

    // Use the functional helpers to get values
    var src := FindMatch(rest, "-s");
    var dst := FindMatch(rest, "-d");
    var proto := FindMatch(rest, "-p");
    var srcPort := FindMatch(rest, "--sport");
    var dstPort := FindMatch(rest, "--dport");
    
    // For Target, we need to find "-j" and parse its value
    var targetMatch := FindMatch(rest, "-j");
    var target: Target;
    var targetOk := false;
    
    if targetMatch.MatchExact? {
       target := ParseTarget(targetMatch.value);
       targetOk := true;
    } else {
       target := TargetReturn;
       // targetOk remains false
    }

    // Strictness check: explicitly use the verified predicate
    var validFlags := ValidTokens(rest);

    if validFlags && targetOk {
       rule := Rule(chain, src, dst, proto, srcPort, dstPort, target, lineNumber, rawLine);
       ok := true;
    } else {
       rule := Rule(chain, src, dst, proto, srcPort, dstPort, target, lineNumber, rawLine);
       ok := false;
    }
  }

  method BuildSmtDocument(rules: seq<Rule>) returns (doc: string)
    // removed ensures |doc| > 0 constraint to allow empty output
  {
    if |rules| == 0 {
      doc := "";
      return;
    }

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

  function IntToString(n: int): string
    decreases if n < 0 then -n else n
  {
    if n == 0 then "0"
    else 
      var value := if n < 0 then -n else n;
      var digits := DigitsToString(value);
      if n < 0 then "-" + digits else digits
  }

  function DigitsToString(n: int): string
    requires n > 0
    decreases n
  {
    var digit := n % 10;
    var rest := n / 10;
    var dStr := DigitToString(digit);
    if rest == 0 then dStr else DigitsToString(rest) + dStr 
  }

  function DigitToString(d: int): string
    requires 0 <= d < 10
  {
    "0123456789"[d .. d+1]
  }

  function BuildRuleConditions(rule: Rule): seq<string>
  {
         var chainLiteral := FormatStringLiteral(rule.chain);
    var c1 := ["(= pkt_chain " + chainLiteral + ")"];
    var c2 := MaybeAppend(c1, "pkt_src", rule.source);
    var c3 := MaybeAppend(c2, "pkt_dst", rule.destination);
    var c4 := MaybeAppend(c3, "pkt_proto", rule.protocol);
    var c5 := MaybeAppend(c4, "pkt_sport", rule.srcPort);
    var c6 := MaybeAppend(c5, "pkt_dport", rule.dstPort);
    c6
  }

  function MaybeAppend(conds: seq<string>, fieldName: string, crit: FieldMatch): seq<string>
  {
    match crit
      case MatchExact(value) =>
        var literal := FormatStringLiteral(value);
        var fragment := "(= " + fieldName + " " + literal + ")";
        conds + [fragment]
      case MatchAny =>
        conds
  }

  function FormatTargetLiteral(target: Target): string
  {
    FormatStringLiteral(TargetToString(target))
  }

  function TargetToString(target: Target): string
  {
    match target
      case TargetAccept => "ACCEPT"
      case TargetDrop => "DROP"
      case TargetReject => "REJECT"
      case TargetReturn => "RETURN"
      case TargetJump(name) => name
  }

  function FormatStringLiteral(text: string): string
  {
    "\"" + EscapeForSmt(text) + "\""
  }

  function EscapeForSmt(text: string): string
  {
     // Recursive definition needed for function
     EscapeForSmtRecursive(text)
  }

  function EscapeForSmtRecursive(text: string): string
    decreases |text|
  {
    if |text| == 0 then ""
    else
      var ch := text[0];
      var rest := EscapeForSmtRecursive(text[1..]);
      if ch == '"' || ch == '\\' then "\\" + text[0..1] + rest
      else text[0..1] + rest
  }

  // Pure function version of FormatRule
  function FormatRule(rule: Rule, index: int): string
    requires index >= 0
  {
    var indexText := IntToString(index);
    var lineText := IntToString(rule.lineNumber);
    var header := "; Rule " + indexText + " (line " + lineText + "): " + rule.original + "\n";
    var def := "(define-fun rule" + indexText + " ((pkt_chain String) (pkt_src String) (pkt_dst String) (pkt_proto String) (pkt_sport String) (pkt_dport String)) Bool\n";
    var conditions := BuildRuleConditions(rule);

    var condBuilder := 
      if |conditions| == 0 then "  true\n"
      else "  (and\n" + JoinLinesIndent(conditions) + "  )\n";

    var closing := ")\n";
    var targetLiteral := FormatTargetLiteral(rule.target);
    var action := "(assert (=> (rule" + indexText + " packet_chain packet_src packet_dst packet_proto packet_sport packet_dport)\n" +
      "            (= packet_action " + targetLiteral + ")))\n";

    header + def + condBuilder + closing + action
  }

  function JoinLinesIndent(lines: seq<string>): string
  {
    if |lines| == 0 then ""
    else "    " + lines[0] + "\n" + JoinLinesIndent(lines[1..])
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
    ensures EqualsIgnoreCase(raw, "ACCEPT") ==> target == TargetAccept
    ensures EqualsIgnoreCase(raw, "DROP") ==> target == TargetDrop
    ensures EqualsIgnoreCase(raw, "REJECT") ==> target == TargetReject
    ensures EqualsIgnoreCase(raw, "RETURN") ==> target == TargetReturn
    ensures !EqualsIgnoreCase(raw, "ACCEPT") && !EqualsIgnoreCase(raw, "DROP") && !EqualsIgnoreCase(raw, "REJECT") && !EqualsIgnoreCase(raw, "RETURN") ==> target == TargetJump(raw)
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
      // Prove it is NOT "RETURN" (needs 'J' vs 'T' check)
      if |raw| >= 3 {
         assert ToUp(raw[2]) == 'J';
         assert ToUp("RETURN"[2]) == 'T';
         assert !EqualsIgnoreCase(raw, "RETURN");
      }
      target := TargetReject;
      return;
    }

    var isReturn := StringsEqualIgnoreCase(raw, "RETURN");
    if isReturn {
      // Prove it is NOT "REJECT"
       if |raw| >= 3 {
         assert ToUp(raw[2]) == 'T';
         assert ToUp("REJECT"[2]) == 'J';
         assert !EqualsIgnoreCase(raw, "REJECT");
      }
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

  // ----------- Strong Specification Helpers -----------

  function Join(parts: seq<string>, delim: string): string
  {
    if |parts| == 0 then ""
    else if |parts| == 1 then parts[0]
    else parts[0] + delim + Join(parts[1..], delim)
  }


  // ----------- Low-Level String Parsing Helpers -----------

  // Splits string into lines. Proving string manipulation correct is complex in Dafny!
  // We need invariants to guide the prover.
  lemma JoinDistributes(parts: seq<string>, delim: string, suffix: string)
    ensures |parts| > 0 ==> Join(parts + [suffix], delim) == Join(parts, delim) + delim + suffix
    ensures |parts| == 0 ==> Join(parts + [suffix], delim) == suffix
  {
    if |parts| == 0 {
       // Base case 0: parts is empty. Join([suffix]) definition leads to "suffix". Correct.
    } else {
        if |parts| == 1 {
           // Base case 1: parts is [p0].
           // Join([p0] + [suffix]) == Join([p0, suffix]).
           // Definition of Join([p0, suffix]) is p0 + delim + Join([suffix]) == p0 + delim + suffix.
           // Join([p0]) + delim + suffix == p0 + delim + suffix.
           // They are equal.
           assert parts + [suffix] == [parts[0], suffix];
        } else {
           // Recursive case: |parts| > 1
           // Key insight: parts + [suffix] starts with parts[0], and the rest is parts[1..] + [suffix]
           var p0 := parts[0];
           var rest := parts[1..];
           
           assert parts == [p0] + rest;
           assert (parts + [suffix]) == [p0] + (rest + [suffix]);
           
           // Expand LHS
           // Join(parts + [suffix]) == Join([p0] + (rest + [suffix]))
           //                        == p0 + delim + Join(rest + [suffix])
           
           // Recurse
           JoinDistributes(rest, delim, suffix);
           
           // Now we know: Join(rest + [suffix]) == Join(rest) + delim + suffix
           // So LHS == p0 + delim + (Join(rest) + delim + suffix)
           
           // Expand RHS
           // Join(parts) + delim + suffix == (p0 + delim + Join(rest)) + delim + suffix
           
           // LHS == RHS by associativity of string concatenation
        }
    }
  }

  // Splits string into lines. 
  // Simplified to only handle '\n' to prove "Join(lines, '\n') == text"
  method SplitLines(text: string) returns (lines: seq<string>)
    requires forall k :: 0 <= k < |text| ==> text[k] != '\r'
    ensures Join(lines, "\n") == text
  {
    if |text| == 0 {
      lines := [""]; 
      return;
    }

    var segments: seq<string> := [];
    var start := 0;
    var i := 0;

    while i < |text|
      decreases |text| - i
      invariant 0 <= start <= i <= |text|
      invariant (if |segments| == 0 then "" else Join(segments, "\n") + "\n") + text[start..i] == text[0..i]
    {
      var ch := text[i];
      if ch == '\n' {
        var part := text[start .. i];
        
        // Assert current state before update
        assert (if |segments| == 0 then "" else Join(segments, "\n") + "\n") + part == text[0..i];

        // Call Lemma to prove: Join(segments + [part]) == ...
        JoinDistributes(segments, "\n", part);

        // We need to show:
        // (if |segments + [part]| == 0 then ... else Join(segments + [part], "\n") + "\n") + text[i+1..i+1] == text[0..i+1]
        // Which simplifies to: Join(segments + [part]) + "\n" == text[0..i] + "\n"
        // And we know text[0..i+1] IS text[0..i] + "\n"
        
        segments := segments + [part];
        start := i + 1;
      }
      i := i + 1;
    }

    var lastPart := text[start .. |text|];
    // Final step logic
    JoinDistributes(segments, "\n", lastPart);
    
    // We knew: (if |segments|==0 then "" else Join(segments)+"\n") + lastPart == text[0..|text|]
    // If |segments| > 0: Join(segments)+"\n" + lastPart == Join(segments + [lastPart])
    // If |segments| == 0: "" + lastPart == Join([lastPart])
    
    segments := segments + [lastPart];
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
