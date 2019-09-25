using System;
using System.Collections;
using System.IO;
using System.Reflection;

public class XML {
    static public compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        dump("program", ast, "", w);
        return ast;
    }

    static private void dump(string name, object i, string prefix, TextWriter wr) {
        if (i == null) {
            wr.WriteLine(prefix + "<" + name + "/>");
            return;
        }
        System.Type t = i.GetType();
        if (name == null) {
            name = t.Name;
        }
        if (t.IsValueType) {
            wr.WriteLine(prefix + "<" + name + ">" + i + "</" + name + ">");
        } else if (t == typeof(string)) {
            wr.WriteLine(prefix + "<" + name + ">" + i + "</" + name + ">");
        } else if (t.IsArray) {
            wr.WriteLine(prefix + "<" + name + ">");
            foreach (object e in (object[])i) {
                dump(null, e, prefix, wr);
            }
            wr.WriteLine(prefix + "</" + name + ">");
        } else if (i is IList) {
            wr.WriteLine(prefix + "<" + name + ">");
            foreach (object e in (IList)i) {
                dump(null, e, prefix, wr);
            }
            wr.WriteLine(prefix + "</" + name + ">");
        } else {
            wr.WriteLine(prefix + "<" + name + ">");
            IHasCoordinate ihc = i as IHasCoordinate;
            if (ihc != null) {
                wr.WriteLine(prefix + "  <begin>" + ihc.begin.ToString() + "</begin>");
            }
            string inner = prefix + "  ";
            if (t.Name != name) {
                wr.WriteLine(inner + "<" + t.Name + ">");
                inner = inner + "  ";
            }
            FieldInfo[] fields = t.GetFields();
            foreach (FieldInfo f in fields) {
                object o = f.GetValue(i);
                string n = f.Name;
                if (f.Name != "parent" && f.Name != "global")
                    dump(f.Name, o, inner + "  ", wr);
            }

            if (t.Name != name) {
                wr.WriteLine(prefix + "  " + "</" + t.Name + ">");
            }
            if (ihc != null) {
                wr.WriteLine(prefix + "  <end>" + ihc.end.ToString() + "</end>");
            }
            wr.WriteLine(prefix + "</" + name + ">");
        }
    }
}
