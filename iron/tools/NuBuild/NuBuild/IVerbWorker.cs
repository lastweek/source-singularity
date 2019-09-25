//---
//- <copyright file="IVerbWorker.cs" company="Microsoft Corporation">
//-     Copyright (c) Microsoft Corporation.  All rights reserved.
//- </copyright>
//---

namespace NuBuild
{
    /
    /
    /
    internal enum IsSync
    {
        /
        /
        /
        Sync,

        /
        /
        /
        Async
    }

    /
    /
    /
    internal interface IVerbWorker
    {
        /
        /
        /
        /
        /
        IsSync isSync();

        /
        /
        /
        /
        /
        /
        /
        void runAsync();

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
        Disposition complete();
    }
}
