//------------------------------------------------------------------------------
// <copyright file="IRegisteredObject.cs" company="Microsoft">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>                                                                
//------------------------------------------------------------------------------

namespace System.Web.Hosting
{
    using System;
    
    public interface IRegisteredObject {
        void Stop(bool immediate);
    }
}
