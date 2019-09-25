// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Purpose:
//
//===========================================================  
namespace System
{

    using System.Runtime.CompilerServices;
    using CultureInfo = System.Globalization.CultureInfo;

    // A Version object contains four hierarchical numeric components: major, minor,
    // build and revision.  Build and revision may be unspecified, which is represented
    // internally as a -1.  By definition, an unspecified component matches anything
    // (both unspecified and specified), and an unspecified component is "less than" any
    // specified component.

    //| <include path='docs/doc[@for="Version"]/*' />
    public sealed partial class Version : ICloneable, IComparable
    {
        private int _Major;
        private int _Minor;
        private int _Build = -1;
        private int _Revision = -1;

        //| <include path='docs/doc[@for="Version.Version"]/*' />
        public Version(int major, int minor, int build, int revision) {
            if (major < 0)
              throw new ArgumentOutOfRangeException("major","ArgumentOutOfRange_Version");

            if (minor < 0)
              throw new ArgumentOutOfRangeException("minor","ArgumentOutOfRange_Version");

            if (build < 0)
              throw new ArgumentOutOfRangeException("build","ArgumentOutOfRange_Version");

            if (revision < 0)
              throw new ArgumentOutOfRangeException("revision","ArgumentOutOfRange_Version");

            _Major = major;
            _Minor = minor;
            _Build = build;
            _Revision = revision;
        }

        //| <include path='docs/doc[@for="Version.Version1"]/*' />
        public Version(int major, int minor, int build) {
            if (major < 0)
                throw new ArgumentOutOfRangeException("major","ArgumentOutOfRange_Version");

            if (minor < 0)
              throw new ArgumentOutOfRangeException("minor","ArgumentOutOfRange_Version");

            if (build < 0)
              throw new ArgumentOutOfRangeException("build","ArgumentOutOfRange_Version");


            _Major = major;
            _Minor = minor;
            _Build = build;
        }

        //| <include path='docs/doc[@for="Version.Version2"]/*' />
        public Version(int major, int minor) {
            if (major < 0)
                throw new ArgumentOutOfRangeException("major","ArgumentOutOfRange_Version");

            if (minor < 0)
                throw new ArgumentOutOfRangeException("minor","ArgumentOutOfRange_Version");

            _Major = major;
            _Minor = minor;
        }

        //| <include path='docs/doc[@for="Version.Version3"]/*' />
        public Version(String version) {
            if ((Object) version == null)
                throw new ArgumentNullException("version");

            String[] parsedComponents = version.Split(new char[] {'.'});
            int parsedComponentsLength = parsedComponents.Length;
            if ((parsedComponentsLength < 2) || (parsedComponentsLength > 4)) throw new ArgumentException("Arg_VersionString");
            _Major = Int32.Parse(parsedComponents[0]);
            if (_Major < 0)
              throw new ArgumentOutOfRangeException("version","ArgumentOutOfRange_Version");

            _Minor = Int32.Parse(parsedComponents[1]);
            if (_Minor < 0)
              throw new ArgumentOutOfRangeException("version","ArgumentOutOfRange_Version");

            parsedComponentsLength -= 2;
            if (parsedComponentsLength > 0) {
                _Build = Int32.Parse(parsedComponents[2]);
                if (_Build < 0)
                  throw new ArgumentOutOfRangeException("build","ArgumentOutOfRange_Version");

                parsedComponentsLength--;
                if (parsedComponentsLength > 0) {
                    _Revision = Int32.Parse(parsedComponents[3]);
                    if (_Revision < 0)
                      throw new ArgumentOutOfRangeException("revision","ArgumentOutOfRange_Version");
                }
            }
        }

        //| <include path='docs/doc[@for="Version.Version4"]/*' />
        public Version()
        {
            _Major = 0;
            _Minor = 0;
        }

        // Properties for setting and getting version numbers
        //| <include path='docs/doc[@for="Version.Major"]/*' />
        public int Major {
            get { return _Major; }
        }

        //| <include path='docs/doc[@for="Version.Minor"]/*' />
        public int Minor {
            get { return _Minor; }
        }

        //| <include path='docs/doc[@for="Version.Build"]/*' />
        public int Build {
            get { return _Build; }
        }

        //| <include path='docs/doc[@for="Version.Revision"]/*' />
        public int Revision {
            get { return _Revision; }
        }

        //| <include path='docs/doc[@for="Version.Clone"]/*' />
        public Object Clone() {
            Version v = new Version();
            v._Major = _Major;
            v._Minor = _Minor;
            v._Build = _Build;
            v._Revision = _Revision;
            return(v);
        }

        //| <include path='docs/doc[@for="Version.CompareTo"]/*' />
        public int CompareTo(Object version)
        {
            if (version == null)
                return 1;

            if (!(version is Version))
                throw new ArgumentException("Arg_MustBeVersion");

            Version v = (Version) version;

            if (this._Major != v._Major)
                if (this._Major > v._Major)
                    return 1;
                else
                    return -1;

            if (this._Minor != v._Minor)
                if (this._Minor > v._Minor)
                    return 1;
                else
                    return -1;

            if (this._Build != v._Build)
                if (this._Build > v._Build)
                    return 1;
                else
                    return -1;

            if (this._Revision != v._Revision)
                if (this._Revision > v._Revision)
                    return 1;
                else
                    return -1;

            return 0;
        }

        //| <include path='docs/doc[@for="Version.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (((Object) obj == null) ||
                (!(obj is Version)))
                return false;

            Version v = (Version) obj;
            // check that major, minor, build & revision numbers match
            if ((this._Major != v._Major) ||
                (this._Minor != v._Minor) ||
                (this._Build != v._Build) ||
                (this._Revision != v._Revision))
                return false;

            return true;
        }

        //| <include path='docs/doc[@for="Version.GetHashCode"]/*' />
        public override int GetHashCode()
        {
            // Let's assume that most version numbers will be pretty small and just
            // OR some lower order bits together.

            int accumulator = 0;

            accumulator |= (this._Major & 0x0000000F) << 28;
            accumulator |= (this._Minor & 0x000000FF) << 20;
            accumulator |= (this._Build & 0x000000FF) << 12;
            accumulator |= (this._Revision & 0x00000FFF);

            return accumulator;
        }

        //| <include path='docs/doc[@for="Version.ToString"]/*' />
        public override String ToString() {
            if (_Build == -1) return(ToString(2));
            if (_Revision == -1) return(ToString(3));
            return(ToString(4));
        }

        //| <include path='docs/doc[@for="Version.ToString1"]/*' />
        public String ToString(int fieldCount) {
            switch (fieldCount) {
            case 0:
                return(String.Empty);
            case 1:
                return(String.Concat(_Major));
            case 2:
                return(String.Concat(_Major,".",_Minor));
            default:
                if (_Build == -1)
                    throw new ArgumentException(String.Format("ArgumentOutOfRange_Bounds_Lower_Upper", "0", "2"), "fieldCount");
                if (fieldCount == 3)
                    return( _Major + "." + _Minor + "." + _Build );

                if (_Revision == -1)
                    throw new ArgumentException(String.Format("ArgumentOutOfRange_Bounds_Lower_Upper", "0", "3"), "fieldCount");

                if (fieldCount == 4)
                    return( Major + "." + _Minor + "." + _Build + "." + _Revision );

                throw new ArgumentException(String.Format("ArgumentOutOfRange_Bounds_Lower_Upper", "0", "4"), "fieldCount");
            }
        }

        //| <include path='docs/doc[@for="Version.operatorEQ"]/*' />
        public static bool operator ==(Version v1, Version v2) {
            if ((Object) v1 == null) {
                if ((Object) v2 == null)
                    return true;
                else
                    return false;
            }
            if ((Object) v2 == null)
               return false;

            return v1.Equals(v2);
        }

        //| <include path='docs/doc[@for="Version.operatorNE"]/*' />
        public static bool operator !=(Version v1, Version v2) {
            return !(v1 == v2);
        }

        //| <include path='docs/doc[@for="Version.operatorLT"]/*' />
        public static bool operator <(Version v1, Version v2) {
            if ((Object) v1 == null)
                throw new ArgumentNullException("v1");
            return (v1.CompareTo(v2) < 0);
        }

        //| <include path='docs/doc[@for="Version.operatorLE"]/*' />
        public static bool operator <=(Version v1, Version v2) {
            if ((Object) v1 == null)
                throw new ArgumentNullException("v1");
            return (v1.CompareTo(v2) <= 0);
        }

        //| <include path='docs/doc[@for="Version.operatorGT"]/*' />
        public static bool operator >(Version v1, Version v2) {
            return (v2 < v1);
        }

        //| <include path='docs/doc[@for="Version.operatorGE"]/*' />
        public static bool operator >=(Version v1, Version v2) {
            return (v2 <= v1);
        }
    }
}
