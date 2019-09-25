using System;
using System.IO;

public delegate compilation VisitorDelegate(compilation ast,
                                            TextWriter w,
                                            string[] args,
                                            MessageWriter msg);

