//---
//- <copyright file="ResultCache.cs" company="Microsoft Corporation">
//-     Copyright (c) Microsoft Corporation.  All rights reserved.
//- </copyright>
//---

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.IO;
    using System.Linq;

    class ResultCache
        : IKnownObjectHash
    {
        private IItemCache itemCache;
        private NuObjContents nuObjectContents;
        private IHasher hasher;

        //- In-memory set records which results we've already fetchOutputObject()'d from cache. This
        //- avoids re-fetching the entire set if we ask for another object in the same
        //- verb's output list. Note that this ignores the hash value of the verb; it assumes that
        //- the hash values don't change across a run of this process.
        private HashSet<IVerb> alreadyFetchedVerbs;

        //- This isn't a CachedHash because we can't fill it by querying it,
        //- only by explicit insertion.
        Dictionary<BuildObject, string> knownObjectHash;

        public ResultCache(IItemCache itemCache, NuObjContents nuObjectContents)
        {
            this.itemCache = itemCache;
            this.nuObjectContents = nuObjectContents;
            this.alreadyFetchedVerbs = new HashSet<IVerb>();
            this.knownObjectHash = new Dictionary<BuildObject, string>();
            this.hasher = BuildEngine.theEngine.getHasher();
        }

        //- Read an output object from the nuobj tree and store it in the cache.
        public BuildObjectValuePointer storeObject(BuildObject obj)
        {
            string contentHash = hasher.hash(obj.getFilesystemPath());
            this.itemCache.StoreItemFromFile(ItemCacheContainer.Objects, contentHash, obj.getFilesystemPath());
            this.knownObjectHash[obj] = contentHash;

            return new BuildObjectValuePointer(contentHash, obj.getRelativePath());
        }

        public void storeResult(string inputHash, ResultSummaryRecord result)
        {
            using (MemoryStream outStream = new MemoryStream())
            {
                using (StreamWriter outWriter = new StreamWriter(outStream))
                {
                    outWriter.Write(result.toXml());
                }

                this.itemCache.StoreItem(ItemCacheContainer.Results, inputHash, outStream.ToArray());
            }
        }

        //- returns record.disposition is Stale if no cached result is available.
        public ResultSummaryRecord fetchResult(string inputHash)
        {
            byte[] result = this.itemCache.FetchItem(ItemCacheContainer.Results, inputHash);
            if (result != null)
            {
                MemoryStream resultStream = new MemoryStream(result);
                try
                {
                    using (StreamReader inReader = new StreamReader(resultStream))
                    {
                        string xmlSummary = inReader.ReadToEnd();
                        return ResultSummaryRecord.fromXml(xmlSummary);
                    }
                }
                catch (System.Xml.XmlException ex)
                {
                    throw new ObjectMissingFromCacheException(inputHash, "Malformed xml: " + ex.ToString());
                }
                finally
                {
                    resultStream.Dispose();
                }
            }
            else
            {
                return new ResultSummaryRecord(new Stale(), new BuildObjectValuePointer[] { }, false);
            }
        }

        //- Fetch an object from the cache and store it in the local
        //- nuobj tree.
        //-
        //- NB BuildObjectValuePointers get stored in untrusted places, so we never
        //- actually use their RelativePath values in filesystem calls.
        //- Instead, we require the caller to supply a local BuildObject where
        //- he expects the ptr to point, and we test for equality, and then
        //- use the obj value for filesystem operations.
        void fetchObject(BuildObjectValuePointer ptr, BuildObject obj)
        {
            //-Console.WriteLine("ResultCache.fetchObject " + obj);
            Util.Assert(obj.getRelativePath().Equals(ptr.relativePath));
            File.Delete(obj.getFilesystemPath());
            this.itemCache.FetchItemToFile(ItemCacheContainer.Objects, ptr.objectHash, obj.getFilesystemPath());
            this.knownObjectHash[obj] = ptr.objectHash;
        }

        //- Contract: call only when output objects are known to be cached
        //- (because fetchResult returned non-Stale).
        public void fetchOutputObjects(IVerb verb, IEnumerable<BuildObjectValuePointer> values, Disposition disp)
        {
            if (this.alreadyFetchedVerbs.Contains(verb))
            {
                return;
            }

            IEnumerable<BuildObject> objects = verb.getOutputs();
            IEnumerable<BuildObject> failureObjs = verb.getFailureOutputs();
            objects = objects.Concat(failureObjs);
            Dictionary<string, BuildObject> objectDict = new Dictionary<string, BuildObject>();
            foreach (BuildObject obj in objects)
            {
                objectDict.Add(obj.getRelativePath(), obj);
            }

            HashSet<BuildObject> recorded = new HashSet<BuildObject>();
            foreach (BuildObjectValuePointer value in values)
            {
                if (objectDict.ContainsKey(value.relativePath))
                {
                    BuildObject obj = objectDict[value.relativePath];
                    obj.prepareObjDirectory();
                    this.fetchObject(value, obj);
                    nuObjectContents.bless(obj, value.objectHash, disp);
                    recorded.Add(obj);
                }
                else
                {
                    throw new Exception("Distressing: some BOVPs aren't in obj.getOutputs");
                }
            }

            IEnumerable<BuildObject> unrecorded = objects.Except(recorded).Except(failureObjs);
            Util.Assert(unrecorded.Count() == 0 || disp is Failed);
            foreach (BuildObject obj in unrecorded)
            {
                nuObjectContents.bless(obj, null, disp);
            }

            this.alreadyFetchedVerbs.Add(verb);
        }

        public string getKnownObjectHash(BuildObject obj)
        {
            string hash;
            bool present = knownObjectHash.TryGetValue(obj, out hash);
            if (!present)
            {
                NuObjValue value = nuObjectContents.getValue(obj);
                if (value != null)
                {
                    if (value.disp is Failed)
                    {
                        return null;
                    }
                    else if (obj is VirtualBuildObject)
                    {
                        hash = "virtual";
                    }
                    else
                    {
                        hash = hasher.hash(obj.getFilesystemPath());
                    }
                    knownObjectHash[obj] = hash;
                }
            }
            return hash;
        }
    }
}
