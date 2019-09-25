



module HLIncrementer {
    datatype State = State_c(value:int);
    static predicate Init(s:State)
        ensures Init(s) == (s.value == 0);
    {
        s.value == 0
    }
    static predicate Unchanged(s:State, s':State)
        ensures Unchanged(s,s') == (s==s');
    {
        s == s'
    }
    static predicate Next(s:State, s':State)
        ensures Next(s,s') == (s'.value == s.value + 1);
    {
        s'.value == s.value + 1
    }
}
