import System.IO
import sys

# A hacky script to print the shortest valid path between a directory and
# another fs object on Win32. Prints the shorter of the absolute and
# relative paths.

def main():
   if len(sys.argv) != 3:
      print "Usage: %s <currentDir> <targetFile>" % sys.argv[0]
      return 2

   sp1 = sys.argv[1]
   sp2 = sys.argv[2]

   if sp2 == sp1:
      print "."
      return 0

   fp1 = System.IO.Path.GetFullPath(sys.argv[1])
   fp2 = System.IO.Path.GetFullPath(sys.argv[2])

   if fp2 == fp1:
      print "."
      return 0

   c1 = fp1.split(System.IO.Path.DirectorySeparatorChar)
   c2 = fp2.split(System.IO.Path.DirectorySeparatorChar)

   if c1[0] != c2[0]:
       print sp2
       return 0

   i = 1
   n = min(c1.Count, c2.Count)
   while (i < n) and c1[i] == c2[i]:
      i = i + 1

   rpc = [".."] * (len(c1) - i) + c2[i:]
   sep = "%c" % System.IO.Path.DirectorySeparatorChar
   rp = sep.join(rpc)
   if len(rp) < len (fp2):
      print rp
   else:
      print sp2

   return 0

if __name__ == "__main__":
   sys.exit(main())
