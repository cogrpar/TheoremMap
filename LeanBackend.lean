import Std.Data.HashMap -- or Lean.Data.HashMap

def version := "1.0.0" 

-- the following function belonging to the String namespace returns the reversed string
def String.reverse (s : String) : String :=
  ⟨s.data.reverse⟩

-- implementation of the strip and rstrip functions for strings
def String.strip (s : String) (c : Char := ' ') : String :=
  ⟨s.data.dropWhile (λ x => x = c)⟩

def String.rstrip (s : String) (c : Char := ' ') : String :=
  ⟨(s.data.reverse.dropWhile (λ x => x = c)).reverse⟩

-- the following function takes a string and returns a new string with all sequences of spaces collapsed to a single space
def collapse_spaces : String → String :=
  λ str =>
    String.foldl
      (λ acc c =>
        if c = ' ' ∧ acc.back = ' ' then acc
        else acc.push c)
      ""
      str

-- the following function splits a string by a delimiter, keeping all terms contained within parentheses intact
def split_terms (input : String) (delim : Char) (num_open_parentheses := 0) (len := input.length) : List String :=
  if len = 0 then -- reached end of input, base case is to return a list with an empty string
    [""]
  else if input.get 0 = '(' then -- if the first character is '(', increment num_open_parentheses and do a recursive call after removing the first character in the input
    let rest_of_split := split_terms (input.drop 1) delim (num_open_parentheses + 1) (len - 1)
    let first_of_rest := 
      match rest_of_split.get? 0 with
      | some first => first
      | none       => ""
    ["(".append first_of_rest].append (rest_of_split.drop 1)
  else if input.get 0 = ')' then -- if the first character is ')', decrement num_open_parentheses and do a recursive call after removing the first character in the input
    let rest_of_split := split_terms (input.drop 1) delim (num_open_parentheses - 1) (len - 1)
    let first_of_rest := 
      match rest_of_split.get? 0 with
      | some first => first
      | none       => ""
    [")".append first_of_rest].append (rest_of_split.drop 1)
  else if input.get 0 = delim ∧ num_open_parentheses = 0 then -- if the first character is the delim and there are no open parentheses (ie not in a term)
    let rest_of_split := split_terms (input.drop 1) delim num_open_parentheses (len - 1) -- do a recursive call after removing the first character in the input
    [""].append rest_of_split -- return a list containing a new term and the result of the recursive call
  else -- other characters
    let rest_of_split := split_terms (input.drop 1) delim num_open_parentheses (len - 1) -- do a recursive call after removing the first character in the input
    let first_of_rest := 
      match rest_of_split.get? 0 with
      | some first => first
      | none       => ""
    [(input.get 0).toString.append first_of_rest].append (rest_of_split.drop 1) -- combine the first character and the first element of the recursive call

-- the following function counts the number of occurrences of a character in a string
def count_occurrences (input : String) (c : Char) : Nat :=
  input.foldl (λ acc char => if char = c then acc + 1 else acc) 0

-- the following list contains lean operators stored in strings
def operators := ["↔", "<->", "→", "->", "∨", "∧", "=", "≠", ">", "<", "≥", ">=", "≤", "<=", "+", "-", "*", "/", "%", "unary_minus", "¬", "^"]

-- the following hashmap ranks lean operators by order of operation
def operator_precedence : Std.HashMap Nat (List String) :=
  -- lowest precedence...
  (((((((((((
    Std.HashMap.empty.insert 
      1  ["↔", "<->", "Iff", ":"]).insert 
      2  ["→", "->"]).insert
      3  ["∨", "Or"]).insert
      4  ["∧", "And"]).insert
      5  ["=", "Eq", "≠", "Ne"]).insert
      6  [">", "<", "≥", ">=", "≤", "<="]).insert
      7  ["+", "-"]).insert
      8  ["*", "/", "%", "×"]).insert
      9  ["unary_minus", "¬", "Not"]).insert
      10 ["^"]).insert
      11 ["∀", "∃"]
  )
  -- to highest precedence

-- this function looks up the precedence of an operator from the above map
def get_precedence (op : String) : Nat :=
  operator_precedence.fold (λ acc k v => if v.contains op then acc + k else acc) 0

-- this function replaces instances of a unary minus with the string "unary_minus"
def make_unary_minus_explicit (input : String) : String :=
  -- add spaces padding all target operators and paretheses to isolate them when splitting terms by ' '
  let input_parentheses_padded := (input.replace "(" " ( ").replace ")" " ) "
  let input_reformatted := operators.foldl (λ str op => str.replace op (" " ++ op ++ " ")) input_parentheses_padded
  
  -- split the input into terms
  let terms := (split_terms input_reformatted ' ').filter (λ str => ¬(String.isEmpty str))

  -- for each term, if it is a minus sign (-) and the previous term is an operator, then replace the minus sign with "unary_minus"
  let updated_terms := terms.foldl (λ output term =>
    if term = "-" then
      let prev_term := 
        match terms.get? (terms.length - 1) with
        | some prev => prev
        | none      => ""
      if operators.contains prev_term ∨ output = "[START]" then -- prev term is operator or this is the first term
        output ++ " unary_minus"
      else
        output ++ " -"
    else
      output ++ " " ++ term
    
  ) "[START]"
  collapse_spaces (updated_terms.drop 7).strip.rstrip

-- the following function removes any redundant parentheses from an expression stored in a string
def remove_redundant_parentheses (input : String) (num_parentheses := count_occurrences input '(') : String :=
  if num_parentheses = 0 then
    collapse_spaces input
  else
    -- add spaces padding all target operators and paretheses to isolate them when splitting terms by ' '
    let input_parentheses_padded := (input.replace "(" " ( ").replace ")" " ) "
    let input_reformatted := make_unary_minus_explicit (operators.foldl (λ str op => str.replace op (" " ++ op ++ " ")) input_parentheses_padded)
    
    -- split the input into terms
    let terms := (split_terms input_reformatted ' ').filter (λ str => ¬(String.isEmpty str))

    -- this variable stores the maximum precedence of the operators not in parentheses
    let max_external_operator := terms.foldl (λ max term => 
      if term.contains '(' then 
        max
      else -- only look at terms not in parentheses
        let precedence := get_precedence term
        if precedence > max then precedence else max
    ) 0 

    -- iterate over each term and simplify it before determining if its parentheses are redundant and adding it to updated_terms
    let updated_terms := terms.foldl (λ output term =>
      if term.contains '(' then 
        let term := (((term.drop 2).reverse).drop 2).reverse -- remove the parentheses from the term
        let term_simplified := remove_redundant_parentheses term (num_parentheses - 1)

        -- add spaces padding all target operators and paretheses to isolate them when splitting terms by ' '
        let term_simplified_formatted := (term_simplified.replace "(" " ( ").replace ")" " ) "
        let term_simplified_formatted := operators.foldl (λ str op => str.replace op (" " ++ op ++ " ")) term_simplified_formatted
        
        -- split the input into terms
        let sub_terms := (split_terms term_simplified_formatted ' ').filter (λ str => ¬(String.isEmpty str))

        -- determine the minimum precedence of the operators for these terms within parentheses
        let min_internal_operator := sub_terms.foldl (λ min term => 
          if term.contains '(' then 
            min
          else -- only look at terms not in parentheses
            let precedence := get_precedence term
            if precedence < min ∧ precedence ≠ 0 then precedence else min
        ) operator_precedence.size
        
        -- if the minimum internal precedence is greater than the maximum external precedence, then the parentheses are redundant
        if min_internal_operator ≥ max_external_operator then
          output ++ " " ++ term_simplified
        else
          output ++ " (" ++ term_simplified ++ ") "
      else output ++ " " ++ term
    ) ""
    (collapse_spaces updated_terms.strip.rstrip).replace "unary_minus " "-"

def imp_str := "→"