using System;
using System.IO;
using System.Diagnostics;
using System.Text;
using System.Reflection;
using System.Reflection.Emit;
using System.Windows.Forms;
using System.Threading;

public class demo {
    [STAThread]
    public static void Main(string[] args) {
        Form form = new Form1();
        c = new Compiler(reader, Console.Error);
        c.LoadVisitor("bind");
        c.LoadVisitor("typecheck");
        c.LoadVisitor("rewrite");
        c.LoadVisitor("emit");
        c.AddVisitor(typeof (demo));
        Application.Run(form);
    }
    static AssemblyBuilder asm = null;
    static ReflectionReader reader = new ReflectionReader();
    static Compiler c = null;
    public static AssemblyBuilder Compile(string code) {
        c.Msg.Count = 0;
        asm = null;
        int count = c.Compile(new StringReader(code), Console.Out, new string[] {});
        if (count == 0 && asm != null) {
            reader.Load(asm);
            return asm;
        }
        return null;
    }
    public static void Run(AssemblyBuilder asm) {
        MethodInfo m = asm.EntryPoint.DeclaringType.GetMethod(asm.EntryPoint.Name);
        try {
            if (m != null)
                m.Invoke(null, null);
        } catch (Exception e) {
            Console.Error.WriteLine("{0}", e.ToString());
        }
    }
    public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            asm = (AssemblyBuilder)ast;
        return ast;
    }
}
