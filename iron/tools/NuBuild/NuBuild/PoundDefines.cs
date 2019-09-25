using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class PoundDefines
    {
        List<string> _definedSymbols;
        string _descr;

        public PoundDefines(IEnumerable<string> definedSymbols)
        {
            _definedSymbols = new List<string>(definedSymbols);
            _definedSymbols.Sort();
            //- NB the null list gets a *null* ToString, which is interpreted as no appLabel.
            _descr = _definedSymbols.Count==0 ? null : "#"+String.Join(",", _definedSymbols);
        }

        public override string ToString()
        {
            return _descr;
        }

        public string getAbstractIdString()
        {
            return _descr == null ? "" : ", " + _descr;
        }

        public override int GetHashCode()
        {
            return _descr.GetHashCode();
        }

        public override bool Equals(object obj)
        {
            if (obj is PoundDefines)
            {
                PoundDefines other = (PoundDefines)obj;
                return _descr == null && other._descr == null
                    || _descr != null && _descr.Equals(other._descr);
            }
            else
            {
                return false;
            }
        }

        internal static string toAppLabel(PoundDefines poundDefines)
        {
            return poundDefines == null ? null : poundDefines.ToString();
        }

        internal static PoundDefines empty()
        {
            return new PoundDefines(new string[] {});
        }

        internal IEnumerable<string> ToDefArgs()
        {
            List<string> args = new List<string>();
            foreach (string symbol in _definedSymbols)
            {
                args.Add("-def");
                args.Add(symbol);
            }
            return args;
        }
    }
}
