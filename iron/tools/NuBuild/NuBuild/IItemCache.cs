//---
//- <copyright file="IItemCache.cs" company="Microsoft Corporation">
//-     Copyright (c) Microsoft Corporation.  All rights reserved.
//- </copyright>
//---

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    /
    /
    /
    /
    /
    /
    /
    /
    /
    public enum ItemCacheContainer
    {
        /
        /
        /
        Sources = 0,

        /
        /
        /
        Objects = 1,

        /
        /
        /
        Results = 2
    }

    /
    /
    /
    public interface IItemCache
    {
        /
        /
        /
        string Name
        {
            get;
        }

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
        byte[] FetchItem(
            ItemCacheContainer container,
            string itemHash);

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
        void FetchItemToFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemDestinationPath);

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
        void StoreItem(
            ItemCacheContainer container,
            string itemHash,
            byte[] contents);

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
        void StoreItemFromFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemSourcePath);

        /
        /
        /
        /
        /
        /
        /
        /
        /
        void DeleteItem(
            ItemCacheContainer container,
            string itemHash);

        /
        /
        /
        /
        /
        /
        HashSet<string> GetItemsInContainer(
            ItemCacheContainer container);

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
        long GetItemSize(
            ItemCacheContainer container,
            string itemHash);
    }
}
