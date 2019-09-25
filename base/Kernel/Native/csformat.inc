/////////////////////////////////////////////////////////////////////////////
//
//  csformat - Shared output format utility between singularity and debugger extension
//
//  Copyright Microsoft Corporation.  All rights reserved.
//


void FormatCSOutput(void * context,
                    char * format, 
                    char * buffer, 
                    int bufferLen,
                    int (*pfprintField)(void * context, char *pszOut, int bufferSize, int aln, int wid, char fmt, int argIdx),
                    char * (*pfStringField)(void * context, int argIdx)) 
{
    char * text = format;
    char *  pmsg = buffer;
    char *  ptxt = text;
    char * endBuffer = buffer + bufferLen - 1;
    while (*ptxt != '\0') {
        
        if (*ptxt == '{') {
            char * pbeg = ptxt;
            bool bad = false;
            ptxt++;

            int ndx = 0;
            int aln = 0;
            int wid = 0;
            char fmt = 'd';

            if (*ptxt == '{') {
                *pmsg++ = *ptxt++;
            }
            else if (*ptxt >= '0' && *ptxt <= '9') {

                // {index,alignment:type width}
                // Get Index
                while (*ptxt >= '0' && *ptxt <= '9') {
                    ndx = ndx * 10 + (*ptxt++ - '0');
                }

                // Get Alignment
                if (*ptxt == ',') {
                    ptxt++;
                    while (*ptxt >= '0' && *ptxt <= '9') {
                        aln = aln * 10 + (*ptxt++ - '0');
                    }
                }

                // Get FormatString
                if (*ptxt == ':') {
                    ptxt++;
                    if (*ptxt >= 'a' && *ptxt <= 'z') {
                        fmt = *ptxt++;
                    }
                    else if (*ptxt >= 'A' && *ptxt <= 'Z') {
                        fmt = *ptxt++ - 'A' + 'a';
                    }
                    while (*ptxt >= '0' && *ptxt <= '9') {
                        wid = wid * 10 + (*ptxt++ - '0');
                    }
                }

                // indirect formatting
                if (*ptxt == '*') {
                    ptxt++;

                    if (pfStringField != NULL) {

                        text = pfStringField(context, ndx);
                        if (text != NULL) {

                            ptxt = text;
                            continue;
                        }
                    }

                }

                // Get closing brace.
                if (*ptxt == '}') {
                    ptxt++;
                }
                else {
                    bad = true;
                }

                int printLength = pfprintField(context, 
                                               pmsg, 
                                               (int)(endBuffer - pmsg), 
                                               aln, 
                                               wid, 
                                               fmt, 
                                               ndx);

                if (printLength >= 0) {

                    pmsg += printLength;

                    if (pmsg > endBuffer) {
                        pmsg = endBuffer;
                    }
                }
                // If the format was bad, then copy it.
                if (bad) {

                    while (pbeg < ptxt) {
                        *pmsg++ = *pbeg++;
                    }
                }
            }
        }
        else if (*ptxt == '}') {
            ptxt++;
            *pmsg++ = *ptxt++;
        }
        else if (*ptxt == '\n') {
            ptxt++;
        }
        else {
            *pmsg++ = *ptxt++;
        }
    }
    *pmsg++ = '\0';
}


