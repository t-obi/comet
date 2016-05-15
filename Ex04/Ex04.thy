theory Ex04
imports Main

begin

section \<open>Exercise Sheet 4\<close>

subsection \<open>Exercise 1\<close>
lemma god_exists: 
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

end
