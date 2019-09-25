
public class AscendingSequence : IInt32Sequence
{
    public AscendingSequence(int first, int step)
    {
        this.next = first;
        this.step = step;
    }

    int next;
    int step;

    public int GetNext()
    {
        int result = next;
        next += step;
        return result;
    }
}

