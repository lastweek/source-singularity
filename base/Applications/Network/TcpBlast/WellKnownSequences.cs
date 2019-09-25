
public class WellKnownSequences
{
    public static IInt32SequenceFactory GetWellKnownSequence(string/*!*/ name)
    {
        name = name.ToLower();
        switch (name) {
            case "fib":
                return delegate { return (IInt32Sequence)new FibonacciSequence(); };

            case "add":
                return delegate { return (IInt32Sequence)new AscendingSequence(0, 1); };

            default:
                return null;
        }
    }
}


public delegate IInt32Sequence/*!*/ IInt32SequenceFactory();
