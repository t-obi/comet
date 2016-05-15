theory Ex03
imports Main

begin

section \<open>Exercise 1\<close>

lemma ex1a: "((\<forall>X. p X) \<and> (\<forall>X. q X) \<Longrightarrow> (\<forall>X. p X \<and> q X))"
proof -
  assume 1: "(\<forall>X. p X) \<and> (\<forall>X. q X)"
  {
    fix a
    from 1 have 2: "(\<forall>X. p X)" by (rule conjunct1)
    from 1 have 3: "(\<forall>X. q X)" by (rule conjunct2)
    from 2 have 4:"p a" by (rule allE)
    from 3 have 5: "q a" by (rule allE)
    from 4 5 have 6: "p a \<and> q a" by (rule conjI)
  }
  from this show ?thesis by (rule allI)
qed

lemma ex1b: "\<forall>X. p X \<Longrightarrow> \<exists>X. p X"
proof -
  assume 1: "\<forall>X. p X"
  fix c
  from 1 have 2: "p c" by (rule allE)
  from 2 have "\<exists>X. p X" by (rule exI)
  thus ?thesis .
qed

lemma ex1c: "\<exists>X. p X \<and> q X \<Longrightarrow> \<exists>X. p X"
proof -
  assume 1: "\<exists>X. p X \<and> q X"
  from 1 obtain c where 2: "p c \<and> q c" by (rule exE)
  from 2 have 3:"p c" by (rule conjunct1)
  from 3 have "\<exists>X. p X" by (rule exI)
  thus ?thesis .
qed

lemma ex1d: "((\<forall>X. p X) \<and> (\<forall>X. q X)) \<longleftrightarrow> (\<forall>X. p X \<and> q X)"
proof -
{
  {
    assume 1: "((\<forall>X. p X) \<and> (\<forall>X. q X))"
    {
      from 1 have 2: "(\<forall>X. p X)" by (rule conjunct1)
      from 1 have 3: "(\<forall>X. q X)" by (rule conjunct2)
      fix a
      from 2 have 4: "p a" by (rule allE)
      from 3 have 5: "q a" by (rule allE)
      from 4 5 have 6: "p a \<and> q a" by (rule conjI)
    }
    from this have 7:"\<forall>X. p X \<and> q X" by (rule allI)
  }
  {
    assume 8: "(\<forall>X. p X \<and> q X)"
    {
      fix a
      from 8 have 9: "p a \<and> q a" by (rule allE)
      from 9 have 10: "p a" by (rule conjunct1)
    }
    from this have 11: "\<forall>X. p X" by (rule allI)
    {
      fix a
      from 8 have 12: "p a \<and> q a" by (rule allE)
      from 12 have 13: "q a" by (rule conjunct2)
    }
    from this have 14: "\<forall>X. q X" by (rule allI)
    from 11 14 have 15: "((\<forall>X. p X) \<and> (\<forall>X. q X))" by (rule conjI)
  }
}
  (*from this show ?thesis by (rule iffI)
   Wie wird das genutzt? *)
oops


section \<open>Exercise 2\<close>

lemma ex2a: " (\<exists>X. \<forall>Y. p X Y) \<longrightarrow> (\<forall>Y. \<exists>X. p X Y) "
proof -
  {
    assume 1: "\<exists>X. \<forall>Y. p X Y"
    {
      fix a
      from 1 obtain b where 2: "\<forall>Y. p b Y" by (rule exE)
      from 2 have 3: "p b a" by (rule allE)
      from 3 have 4: "\<exists>X. p X a" by (rule exI)
    }
    from this have 5: "\<forall>Y. \<exists>X. p X Y" by (rule allI)
  }
  from this show ?thesis by (rule impI)
qed

lemma ex2b: " (\<forall>X. p X \<longrightarrow> q) \<longleftrightarrow> ((\<exists>X. p X) \<longrightarrow> q)"
proof -
    (* want to show two cases: a\<rightarrow>b and b\<rightarrow>a to get a<->b *)
    assume 1:"\<forall>X. p X \<longrightarrow> q"
    fix a
    from 1 have 2: "p a \<longrightarrow> q" by (rule allE)
    assume 3:"p a"
    {
      from 3 have 5: "(\<exists>X. p X)" by (rule exI)
      from 2 3 have 4: "q" by (rule mp)
    }
    from this have 6:"(\<exists>X. p X) \<longrightarrow> q" by (rule impI)
    
    (*assume 7: "(\<exists>X. p X) \<longrightarrow> q"
    from 7 obtain b where 8: "(p b) \<longrightarrow> q " by (rule exE)*)

oops


lemma ex2c: " ((\<forall>X. p X) \<or> (\<forall>X. q X)) \<longleftrightarrow> (\<forall>X. (p X \<or>q X))"
nitpick
(* Counter Model:
  Nitpick found a counterexample for card 'a = 5:

  Free variables:
    p = (\<lambda>x. _)
        (a\<^sub>1 := False, a\<^sub>2 := False, a\<^sub>3 := True, a\<^sub>4 := True, a\<^sub>5 := True)
    q = (\<lambda>x. _)
        (a\<^sub>1 := True, a\<^sub>2 := True, a\<^sub>3 := False, a\<^sub>4 := False, a\<^sub>5 := False)
*)
oops

lemma ex2d: " ((\<exists>X. p X) \<or> (\<exists>X. q X)) \<longleftrightarrow> (\<exists>X. (p X \<or> q X)) "
proof -
  assume 1: "\<exists>X. p X"
  from 1 obtain a where 2: "p a" by (rule exE)
  from 2 have 3: "p a \<or> q a" by (rule disjI1)
  from 3 have 4: "\<exists>X. (p X \<or> q X)" by (rule exI)

  assume 5: "\<exists>X. q X"
  from 5 obtain b where 6: "q b" by (rule exE)
  from 6 have 7: "p b \<or> q b" by (rule disjI2)
  from 7 have 8: "\<exists>X. (p X \<or> q X)" by (rule exI)
oops

lemma ex2e: "( \<forall>X. \<exists>Y. p X Y ) \<longrightarrow> (\<exists>Y. \<forall>X. p X Y)"
nitpick
(* Counter Model:
Nitpick found a counterexample for card 'a = 2 and card 'b = 2:

  Free variable:
    p = (\<lambda>x. _)
        (a\<^sub>1 := (\<lambda>x. _)(b\<^sub>1 := False, b\<^sub>2 := True),
         a\<^sub>2 := (\<lambda>x. _)(b\<^sub>1 := True, b\<^sub>2 := False))
  Skolem constants:
    \<lambda>Y. X = (\<lambda>x. _)(b\<^sub>1 := a\<^sub>1, b\<^sub>2 := a\<^sub>2)
    \<lambda>X. Y = (\<lambda>x. _)(a\<^sub>1 := b\<^sub>2, a\<^sub>2 := b\<^sub>1)
*)
oops

lemma ex2f: "(\<not>(\<forall>X. p X)) \<longleftrightarrow> (\<exists>X. \<not>p X)"
proof -
  assume 1: "\<forall>X. p X"
  fix a
  from 1 have 2: "p a" by (rule allE)

oops


section \<open>Exercise 3\<close>

lemma ex3a: " (\<exists>X. \<forall>Y. p X Y) \<longrightarrow> (\<forall>Y. \<exists>X. p X Y) "
proof -
  {
    assume 1: "\<exists>X. \<forall>Y. p X Y"
    {
      fix a
      from 1 obtain b where "\<forall>Y. p b Y" by (rule exE)
      from this have "p b a" by (rule allE)
      from this have "\<exists>X. p X a" by (rule exI)
    }
    from this have "\<forall>Y. \<exists>X. p X Y" by (rule allI)
  }
  from this show ?thesis by (rule impI)
qed

end
