using System;

public class FibonacciSequence : IInt32Sequence
{
    long last;
    long beforeLast;
    
    public FibonacciSequence()
    {
        last = 1;
        beforeLast = 1;
    }
    
    /// <summary>
    /// Returns the next number in the Fibonacci sequence, modulo 2^31.
    /// </summary>
    public int GetNext()
    {
        long sum = unchecked(last + beforeLast);
        beforeLast = last;
        last = sum;
        
        return (int)(0x7fffffff & beforeLast);
    }
}

 
