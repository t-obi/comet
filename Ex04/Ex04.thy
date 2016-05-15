theory Ex04
imports Main

begin

section \<open>Exercise Sheet 4\<close>

subsection \<open>Exercise 1 — Onthological Argument 1\<close> 
lemma 
  assumes 1: "\<not>god_exists \<longrightarrow> \<not>(praying \<longrightarrow> answered)"
  assumes 2: "\<not>praying"
  shows "god_exists"
proof -
  {
    assume "\<not>god_exists"
    from 1 this have 3:"\<not>(praying \<longrightarrow> answered)" by (rule mp)
    {
      assume praying
      from 2 this have answered by (rule notE)
    }
    from this have "praying \<longrightarrow> answered" by (rule impI)
    from 3 this have False by (rule notE)
  }
  from this show ?thesis by (rule ccontr)
qed


subsection \<open>Exercise 2 — Induction proofs\<close>

subsubsection \<open>a\<close>

fun sum_n :: "nat \<Rightarrow> nat" where
  "sum_n 0 = 0"
| "sum_n (Suc n) = (Suc n) + sum_n n"

lemma ex2a: "sum_n n = (n * (n + 1)) div 2"
proof (induct n)
  case ia: 0
  have "sum_n 0 = 0" by simp
  have "... = 0 * (0+1)" by simp
  have "... = (0 * (0+1)) div 2" by simp
  thus ?case by simp
next
  case iv:(Suc n)
  have "sum_n (Suc n) = Suc n + sum_n n" by simp
  have "... = Suc n + (n * (n+1)) div 2" using iv by simp
  have "... = (2 * Suc n + (n * (n+1))) div 2" by simp
  have "... = (2 * n + 2  + n * n + n) div 2" by simp
  have "... = ((n + 1) * (n + 2)) div 2" by simp
  have "... = (Suc n * ((n + 1) +1)) div 2" by simp
  have "... = Suc n * (Suc n + 1) div 2" by simp
  thus ?case using iv  by simp
qed

subsubsection \<open>b\<close>

fun sum_n_square ::  "nat \<Rightarrow> nat" where
  "sum_n_square 0 = 0"
| "sum_n_square (Suc n) = sum_n_square n + Suc n * Suc n"

lemma ex2b:"sum_n_square n = (n * (n + 1) * (2 * n + 1)) div 6"
proof (induct n)
  case ia: 0
  have "sum_n_square 0 = 0" by simp
  have "... = (0 * (0 + 1) * 2 * 0 * (0 + 1)) div 6" by simp
  thus ?case by simp
next
  case iv: (Suc n)
  have "sum_n_square (Suc n) = sum_n_square n + Suc n * Suc n" by simp
  have "... = (n * (n + 1) * (2 * n + 1)) div 6 + (n + 1) * (n + 1)" using iv by simp
  have "... = (n * (n + 1) * (2 * n + 1) + (n + 1) * (n + 1) * 6) div 6" by (simp add: distrib_left)
  have "... = ((n + 1) * n * (2 * n + 1) + (n + 1) * (n + 1) * 6) div 6" by simp
  have "... = ((n + 1) * (n * (2 * n + 1) + (n + 1) * 6)) div 6" by (simp add: Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules)
  have "... = ((n + 1) * (2 * n * n + n + 6 * n + 6)) div 6" by (simp add: distrib_left)
  have "... = ((n + 1) * (2 * n * n + 3 * n + 4 * n + 6)) div 6" by simp
  have "... = ((n + 1) * (n * (2 * n + 3) + 2 * (2 * n + 3))) div 6" by (simp add: distrib_left)
  have "... = ((n + 1) * (2 * n + 3) * (n + 2)) div 6" by (simp add: Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules)
  have "... = ((n + 1) * (2 * n + 1 + 2) + (n + 1 + 1)) div 6" by simp
  have "... = (Suc n * (2 * Suc n + 2) * (Suc n + 1)) div 6" by simp
  thus ?case using iv by simp
oops




subsection \<open>Exercise 3 — The rich grandparent\<close>

text \<open>The following riddle is valid in classical logic:\\
{\it
If every poor person has a rich parent,\\
then there is a rich person who has a rich grandparent.
}
\<close>

lemma exists_rich_person:
assumes 1:"\<forall>X. \<not>rich X \<longrightarrow> rich (parent X)"
shows "\<exists>X. rich X"
proof cases
  fix a
  assume "rich a"
  thus "\<exists>X. rich X" by (rule exI)
next
  fix a
  assume "\<not>rich a"
  from 1 this have "rich(parent a)" by simp
  thus "\<exists>X. rich X" by (rule exI)  
qed

lemma exists_rich_grandparent:
assumes 1:"\<forall>X. \<not>rich X \<longrightarrow> rich (parent X)"
shows "\<exists>X. rich(parent(parent X) \<and> rich X)"
proof cases
  fix a
  assume assumption: "\<not>rich a"
  from 1 have 2: "\<not>rich a \<longrightarrow> rich(parent a)" by (rule allE)
  from assumption 2 have 3: "rich (parent a)" by simp


oops
end
