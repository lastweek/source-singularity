/*
  public static BigInteger @asm__BitwiseXor(BigInteger a, BigInteger b) {
      return a ^ b;
  }
  public static BigInteger @asm__BitwiseAnd(BigInteger a, BigInteger b) {
      return a & b;
  }
  public static BigInteger @asm__BitwiseOr(BigInteger a, BigInteger b) {
      return a | b;
  }
  public static BigInteger @asm__LeftShift(BigInteger a, BigInteger b) {
      BigInteger mask = 1;    
      mask = mask << 32;
      mask -= 1;  
      return mask & (a << (int)b);
  }
  public static BigInteger @asm__RightShift(BigInteger a, BigInteger b) {
      return a >> (int)b;
  }
  public static BigInteger @asm__BitwiseNot(BigInteger a) {
      return ~a;
  }
  public static BigInteger @asm__RotateRight(BigInteger a, BigInteger b) {
      BigInteger mask = 1;    
      mask = mask << 32;
      mask -= 1; 
      int amount = (int)b;
      return mask & ((a >> amount) | (a << (32 - amount)));
  }
  public static BigInteger @asm__RotateLeft(BigInteger a, BigInteger b) {
      BigInteger mask = 1;    
      mask = mask << 32;
      mask -= 1; 
      int amount = (int)b;
      return mask & ((a << amount) | (a >> (32 - amount)));
  }
  public static BigInteger @asm__Add(BigInteger a, BigInteger b) {
      BigInteger pow32 = 2;
      pow32 = BigInteger.Pow(pow32, 32);
      return (a + b) % pow32;
  }
*/

