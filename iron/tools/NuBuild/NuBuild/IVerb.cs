//---
//- <copyright file="IVerb.cs" company="Microsoft Corporation">
//-     Copyright (c) Microsoft Corporation.  All rights reserved.
//- </copyright>
//---

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Xml;

    /
    /
    /
    internal interface IVerb
        : IComparable
    {
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp);

        /
        /
        /
        /
        /
        /
        /
        /
        IEnumerable<IVerb> getVerbs();

        /
        /
		/
        /
        /
		/
		/
        /
        /
        IEnumerable<BuildObject> getOutputs();

        /
        /
		/
		/
		/
        /
        /
        IEnumerable<BuildObject> getFailureOutputs();

        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        AbstractId getAbstractIdentifier();

        /
        /
        /
        /
        IVerbWorker getWorker();

        /
        /
        /
        /
        /
        Presentation getPresentation();

        /
        /
        /
        /
        /
        /
        /
        /
        Presentation getRealtimePresentation(Disposition disposition);

        /
        /
        /
        /
        /
        /
        /
        void writeTimingXml(XmlWriter xmlWriter);

        /
        /
        /
        /
        /
        /
        /
        void writeDebugXml(XmlWriter xmlWriter);
    }
}
