using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class SourcePath
        : BuildObject
    {
        public enum SourceType {
            sourceTypeSrc,
            sourceTypeTools,
            sourceTypeBinTools, //- probably don't really want this in the long run, since we can build these.
            //- sourceTypeUnchecked? dangerous
            sourceTypePrebakedObjExpediency   //- used to point at bootloader, until we can get an nmake verb working. TODO remove
        };

        private void checkPrefix(SourceType sourceType, SourceType matchType, string prefix)
        {
            if (sourceType == matchType)
            {
                if (!path.StartsWith(prefix))
                {
                    throw new UserError(String.Format(
                        "Source path {0} should begin with {1}",
                        this.path, prefix));
                }
            }

        }

        private SourceType _sourceType;

        public SourcePath(string inpath, SourceType sourceType = SourceType.sourceTypeSrc)
            : base(inpath, IsSourcePath.Yep)
        {
            //- Sanity checks.
            checkPrefix(sourceType, SourceType.sourceTypeSrc, BuildEngine.theEngine.getSrcRoot());
            checkPrefix(sourceType, SourceType.sourceTypeTools, BuildEngine.theEngine.getToolsRoot());
            checkPrefix(sourceType, SourceType.sourceTypeBinTools, BuildEngine.theEngine.getBinToolsRoot());
            checkPrefix(sourceType, SourceType.sourceTypePrebakedObjExpediency, "obj");   //- TODO killme

            _sourceType = sourceType;
            _isTrusted = getRelativePath().StartsWith(
                Path.Combine(BuildEngine.theEngine.getSrcRoot(), BuildEngine.VerveTrustedSpecDir));
        }

        public SourcePath getNewSourcePath(string inpath)
        {
            return new SourcePath(Path.Combine(getDirPath(), inpath), _sourceType);
        }

        public string getDirRelativeToSrc()
        {
            string dirname = getDirPath();
            int slash = dirname.IndexOf('\\');
            Util.Assert(slash >= 0);
            return dirname.Substring(slash + 1);
        }
    }
}
