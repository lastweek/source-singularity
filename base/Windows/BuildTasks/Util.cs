// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using System.Text;

namespace Microsoft.Singularity.BuildTasks
{
    sealed class Util
    {
        static readonly char[] _whitespace = { ' ', '\t' };

        public static string AddQuotesIfNecessary(string text)
        {
            if (NeedsQuotes(text))
                return "\"" + text + "\"";
            else
                return text;
        }

        public static bool NeedsQuotes(string text)
        {
            return text.Length != 0 && text.IndexOfAny(_whitespace) != -1 && !Char.IsWhiteSpace(text[0]);
        }

        public static void DeleteFileIgnoreErrors(string path)
        {
            try {
                File.Delete(path);
            }
            catch (IOException) {
            }
        }

        public static bool ValidateCSharpIdentifier(string id, bool allowdots)
        {
            if (String.IsNullOrEmpty(id))
                return false;

            if (!Char.IsLetter(id[0]))
                return false;

            for (int i = 1; i < id.Length; i++) {
                char c = id[i];
                if (!(Char.IsLetterOrDigit(c) || c == '_' || c == '$' || (allowdots && c == '.')))
                    return false;
            }

            return true;
        }

    }
}
