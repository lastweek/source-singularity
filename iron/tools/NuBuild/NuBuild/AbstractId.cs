using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild {
    class AbstractId {
        const int MASTER_VERSION = 2;   //- Bump this to invalidate every verb in all caches.

        string verb_name;
        int version;
        string abstract_only;
        //- PoundDefines should appear in both abstract and concrete descriptions:
        //- abstract because we run one verb with multiple poundDefine configurations,
        //- and concrete because the variation appears only in this parameter to the
        //- verb, not in any input file contents.
		PoundDefines poundDefines;
        string concrete;
        public AbstractId(string verb_name, int version, string abstract_only, PoundDefines poundDefines = null, string concrete=null) {            
            this.verb_name = verb_name;
            this.version = version + MASTER_VERSION;
            this.abstract_only = abstract_only;
            this.poundDefines = poundDefines==null ? PoundDefines.empty() : poundDefines;
            this.concrete = concrete;
        }

        public override bool Equals(object obj) {
            if (obj is AbstractId) {
                AbstractId other = (AbstractId)obj;
                return verb_name == other.verb_name
                    && version == other.version
                    && abstract_only == other.abstract_only 
                    && poundDefines.Equals(other.poundDefines)
                    && concrete == other.concrete;
            } else {
                return false;
            }
        }

        public override int GetHashCode() {
            return ToString().GetHashCode();
        }

        public override string ToString() {
            if (concrete == null) {
                return String.Format("{0}(#{1},{2},{3})", verb_name, version, abstract_only, poundDefines.getAbstractIdString());
            } else {
                return String.Format("{0}(#{1},{2},{3},{4})", verb_name, version, abstract_only, poundDefines.getAbstractIdString(), concrete);
            }
        }

        public int CompareTo(object other) {
            return ToString().CompareTo(((AbstractId)other).ToString());
        }

        public string getConcreteId() {
            //- The entire purpose of this class is to avoid encoding the input filename in a verb's concrete identity,
            //- instead encoding it via the input's hash. That enables two verbs to have the same hash when they have
            //- the same configuration, and hence converge -- we can reuse the outputs.
            
            
            
            return ToString();





        }
    
    }
}
