section \<open>Example theory file for getting acquainted with Isabelle\<close>
(*<*)
theory Example
imports Main

begin
(*>*)
subsection \<open>Terms\<close>
text \<open>
  We can write logical formulae and terms in the usual notation.
  Connectives such as @{text "\<not>"},@{text "\<or>"}, @{text "\<and>"} etc. can be typed using the backslash
  @{text "\\"} followed by the name of the sign. I.e. @{text "\\not"} for @{text "\<not>"}.
  Note that during typing @{text "\\not"} at some point there will be a pop-up menu
  offering you certain auto completion suggestions that you can accept by
  pressing the tab key.
\<close>



subsection \<open>Types\<close>
text \<open>
  All terms (and also constant symbols, variables etc.) are associated
  a type. The type @{type "bool"} is the type of all Boolean-values objects
  (e.g. truth values).
  New types can be inserted at will.
\<close>

typedecl "i" -- "Create a new type i for the type of individuals"


subsection \<open>Constants\<close>
text \<open>
  New constants can be defined using the @{text "consts"} keyword.
  You need to specify the type of the constant explicitly.
\<close>

subsection \<open>Terms and Formulas\<close>
text \<open>
  In higher-order logic (HOL), terms are all well-formed expressions
  that can be expressed within the logic. A term has a unique type, such
  as in @{term "f(A) :: i"} where the term @{term "f(A)"} has type
  @{type "i"}. Terms of type @{type "bool"} are called "formulas".
\<close>

subsubsection \<open>Example formula 1\<close>
text \<open>If it's raining the street will get wet\<close>

consts raining :: "bool" -- "constant symbol for raining"
consts wet :: "i \<Rightarrow> bool" -- "predicate symbol for wet"
consts street :: "i" -- "constant symbol for the street"

prop "raining \<longrightarrow> wet(street)" -- "raining implies street-is-wet"


subsubsection \<open>Example formula 2\<close>
consts good :: "i \<Rightarrow> bool" -- "predicate symbol for being good"

prop "good(A)" -- "A is good"
text \<open>A is a free variable of the above term, hence it is not closed\<close>

subsubsection \<open>Example formula 3\<close>

prop "\<forall>A. good(A)" -- "everything is good"
text \<open>A is a a bound variable of the above term, which is universally qualified.\<close>


subsection \<open>Proofs\<close>
text \<open>We will learn how to formalize proofs in Isabelle throughout this course.\<close>

subsubsection \<open>Proofs with handy keywords\<close>

theorem MyFirstTheorem:
  assumes "A"
  shows "B \<longrightarrow> A"
proof -
  {
    assume "B"
    from assms have "A" by - -- "Iterate the fact that A holds by assumptions using the - sign"
  }
  then have "B \<longrightarrow> A" by (rule impI)
  thus ?thesis .
qed

subsubsection \<open>Proofs with labels\<close>

theorem MyFirstTheorem2:
  assumes 1: "A"
  shows "B \<longrightarrow> A"
proof -
  {
    assume "B"
    from 1 have "A" by -
  } note 2 = this
  from 2 have "B \<longrightarrow> A" by (rule impI)
  thus ?thesis .
qed


subsubsection \<open>Using the proofs\<close>
text \<open>
  We can now derive simple facts of the above theorem.
\<close>

corollary ThatFollowsDirectly:
  assumes "A"
  shows "P(A) \<longrightarrow> A"
using assms by (rule MyFirstTheorem[where B = "P(A)"])

theorem excludedMiddle:
  shows "A \<or> \<not>A"
proof -
  {
    assume 1: "\<not>(A \<or> \<not>A)"
    {
      assume 2: "\<not>A"
      from 2 have 3: "A \<or> \<not>A" by (rule disjI2)
      from 1 have 4: "\<not>(A \<or> \<not>A)" by -
      from 4 3 have "False" by (rule notE)
    }
    from this have 5: "A" by (rule ccontr)
    from 5 have 6: "A \<or> \<not>A" by (rule disjI1)
    from 1 6 have "False" by (rule notE)
  }
  from this have "A \<or> \<not>A" by (rule ccontr)
  thus ?thesis .
qed

subsection \<open>Exercise 1c: logical expressions natural language3\<close>

prop "\<exists>ship. huge(ship) \<and> blue(ship)" 
prop "\<not>shining() \<longrightarrow> sad(me)"
prop "raining \<or> not_raining"
prop "going(she) \<longrightarrow> going(me) \<and> \<not>going(she) \<longrightarrow> \<not>going(me)"

section \<open>Exercise 2\<close>

subsection \<open>a)\<close>

theorem A:
  assumes 1: "A \<and> B \<longrightarrow> C"
  assumes 2: "B \<longrightarrow> A"
  assumes 3: "B"
  shows "C"
proof -
  from 2 3 have 4: "A" by (rule mp)
  from 4 3 have 5: "A \<and> B" by (rule conjI)
  from 1 5 have 6: "C" by (rule mp)
  thus ?thesis.
qed

subsection \<open>b)\<close>
theorem B:
  assumes 1: "A"
  shows "B \<longrightarrow> A "
proof -
  {
    assume "B"
    from 1 have "A" by -
  } note 2 = this
  from 2 have 3: "B \<longrightarrow> A" by (rule impI)
  thus ?thesis.
qed

subsection \<open>c)\<close>
theorem C:
  assumes 1: "A\<longrightarrow>(B\<longrightarrow>C)"
  shows "B \<longrightarrow> (A \<longrightarrow>C)"
proof -
  {
    assume 2: "B"
    {
     assume 3: "A"
     from 1 3 have 4: "B\<longrightarrow>C " by (rule mp)
     from 4 2 have 5: "C" by (rule mp)
    }
    from this have "A \<longrightarrow> C" by (rule impI)
  }
  from this have "B \<longrightarrow> (A \<longrightarrow> C)" by (rule impI)
  thus ?thesis.
qed


subsection \<open>d)\<close>
theorem D:
  assumes 1: "\<not>A"
  shows "A \<longrightarrow> B"
proof -
  {
    assume 2: "A"
    {
     assume 3: "\<not>B"
     from 1 have 4: "\<not>A" by -
     from 2 have 5: "A" by -
     from 4 5 have "False" by (rule notE)
    }
    from this have "\<not>\<not>B" by (rule notI)
    from this have "B" by (rule notnotD)
  }
  from this have "A \<longrightarrow> B" by (rule impI)
  thus ?thesis.
qed

(*<*)
end
(*>*)