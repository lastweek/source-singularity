// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using ProductStudio;

namespace TestExport
{
    internal class TestExporter
    {
        private static readonly string[] DEFAULT_ARGS = new string[] { "-o", "BVT", "foo.tst" };
        //private static readonly string[] DEFAULT_ARGS = new string[] { "-h" };

        private const string TITLE_FORMAT = "{0}!{1}::{2}";

        // Query in Xml Format which retrieves all unassigned bugs
        private static readonly string QUERY_ACTIVE =
                    "<Query><Expression Column='Test Status' Operator='equals'>" +
                    "<String>Active</String></Expression></Query>";
        private static readonly string QUERY_PROFILE =
            "<Query><Group GroupOperator='and'>"+
                "<Expression Column='Test Status' Operator='equals'><String>Active</String></Expression>" +
                "<Expression Column='Test Type' Operator='equals'><String>Automated</String></Expression>" +
                "<Expression Column='Test Profiles' Operator='has'>" +
                    "<Expression Column='Profiles value' FieldType='16' Operator='equals'><String>{0}</String></Expression>" +
                "</Expression></Group></Query>";

//        private static readonly string QUERY_PROFILEy =
//    "<Query><Expression Column='Test Profiles' Operator='has'>" +
//                "<Expression Column='Profiles value' FieldType='16' Operator='equals'><String>{0}</String></Expression>" +
//    "</Expression></Query>";

//        private static readonly string QUERY_PROFILEx =
//            "<Query><Expression Column='Test Profiles' Operator='has'><Group GroupOperator='or'>" +
//                        "<Expression Column='Test Profile value' FieldType='16' Operator='equals'><String>{0}</String></Expression>" +
//            "</Group></Expression></Query>";

        // Fields to retrieve and fields to sort by.
        private static readonly string[] TEST_CASE_FIELDS =
            new string[] { "Title", "Test Module", "Test Suite", "TestCase", "Test Timeout", "Test Known Failure", "Order" };
        private static readonly string[] TEST_CASE_SORT = new string[] {"Order", "Test Module", "Test Suite", "TestCase"};

        private Datastore m_psDataStore;
        private Directory m_psDirectory;
        private string m_profile = "";
        private Hashtable m_existing;
        private int m_existedCount = 0;
        private int m_createdCount = 0;

        private TestExporter(Directory psDirectory, Datastore psDataStore)
        {
            m_psDataStore = psDataStore;
            m_psDirectory = psDirectory;
            m_existing = CurrentTests();
        }

        [STAThread]
        private static int Main(string[] args)
        {
            if (args.Length == 0) {
                args = DEFAULT_ARGS;
            }
            // Connect to the directory with your current
            // domain under your credentials .
            Directory psDirectory = new DirectoryClass();
            try {
                psDirectory.Connect("", "", "");

                Product psProduct = psDirectory.GetProductByName("Singularity");
                Datastore psDataStore = psProduct.Connect("", "", "");

                TestExporter t = new TestExporter(psDirectory, psDataStore);
                switch (args[0]) {
                    case "-i":
                        if (args.Length < 2) {
                            break;
                        }
                        t.ImportProfile(args[1]);
                        t.Report();
                        return 0;
                    case "-o":
                        if (args.Length < 3) {
                            break;
                        }
                        t.ExportProfile(args[1], args[2]);
                        return 0;
                    case "-h":
                        t.QueryTestCases();
                        return 0;
                    default:
                        break;
                }
                Console.WriteLine("Usage: TestExport -i <testprofile> | -o <testType> <testprofile>");
                return -1;
            }
            catch (Exception e) {
                Console.WriteLine("Error: {0}", e.Message);
                return -1;
            }
            finally {
                psDirectory.Disconnect();
            }
        }

        private void ImportProfile(string filename)
        {
            XmlReader r = XmlReader.Create(filename);
            m_profile = filename;
            string module = null;
            string suite = null;
            string testcase = null;
            while (r.Read()) {
                if (r.NodeType != XmlNodeType.Element) {
                    continue;
                }
                string optName = r.GetAttribute("Name");
                switch (r.Name.ToLower()) {
                    case "suite":
                        suite = optName;
                        break;
                    case "module":
                        module = optName;
                        break;
                    case "test":
                        testcase = optName;
                        if (module != null && suite != null && testcase != null) {
                            MakeTestCase(module, suite, testcase);
                        }
                        break;
                    default:
                        break;
                }
            }
        }

        private void Report()
        {
            Console.WriteLine("Created test cases: {0}.  Ignored duplicate test cases: {1}.", m_createdCount, m_existedCount);
        }

        private void MakeTestCase(string module, string suite, string testcase)
        {
            string key = TestKey(module, suite, testcase);
            if (m_existing.ContainsKey(key)) {
                m_existedCount++;
                return;
            }
            // Create a new datastore instance.
            DatastoreItemList psDataList = new DatastoreItemListClass();
            psDataList.Datastore = m_psDataStore;

            // Create a blank Test Case
            psDataList.CreateBlank(PsDatastoreItemTypeEnum.psDatastoreItemTypeTestCase);
            DatastoreItem psDataItem = psDataList.DatastoreItems.Add(null, PsApplyRulesMask.psApplyRulesAll);

            // Set fields for the Test Case
            Fields psFields = psDataItem.Fields;
            psFields["Title"].Value = key;
            psFields["TreeID"].Value = TreeIDFromPath(m_psDataStore.RootNode, "OS");
            // psFields["TCMTreeID"].Value = -200;
            psFields["Test Status"].Value = "Active";
            //psFields["Test Priority"].Value = 2;
            psFields["Test Module"].Value = module;
            psFields["Test Suite"].Value = suite;
            psFields["TestCase"].Value = testcase;
            // psFields["Test Class"].Value = "Boundary";
            // psFields["Test Type"].Value = "Automatic";
            // psFields["Frequency"].Value = "Daily";
            psFields["Owner"].Value = "Active";
            psFields["Description"].Value = "A test case generated from profile " + m_profile;

            //  Let's make sure all fields are valid before saving
            bool hasInvalidField = false;
            foreach (Field psField in psDataItem.Fields) {
                if (psField.Validity != PsFieldStatusEnum.psFieldStatusValid) {
                    hasInvalidField = true;
                    Console.WriteLine("Invalid Field '{0}': {1}", psField.Name, psField.Validity.ToString());
                    Console.WriteLine("Current Value: '{0}'", psField.Value);
                    Console.WriteLine();
                }
            }

            if (hasInvalidField) {
                throw (new ApplicationException("Invalid Field(s) were found.  Could not update."));
            }
            else {
                psDataItem.Save(true);
                int testCaseID = Convert.ToInt32(psFields["ID"].Value);
                Console.WriteLine("Test Case #{0} {1} Successfully Created.", testCaseID, key);
            }
            m_createdCount++;
        }

        private static string TestKey(object module, object suite, object testcase)
        {
            return string.Format(TITLE_FORMAT, module, suite, testcase);
        }

        private void QueryTestCases()
        {
            // Set up the query.
            Query psQuery = new QueryClass();
            psQuery.CountOnly = false;
            psQuery.SelectionCriteria = QUERY_ACTIVE;
            psQuery.DatastoreItemType = PsDatastoreItemTypeEnum.psDatastoreItemTypeTestCase;

            // Bind the query and Datastore to our
            // DatastoreItemList.
            DatastoreItemList psDataList = new DatastoreItemListClass();
            psDataList.Query = psQuery;
            psDataList.Datastore = m_psDataStore;

            // Get the field definitions so we can specify
            // them in the result and sort list.
            // You can also use the GetEnumerator to
            // enumerate the fields.
            FieldDefinitions psFields = m_psDataStore.FieldDefinitions;
            foreach (FieldDefinition item in psFields) {
                Console.WriteLine(item.Name);
            }

            // Add fields with the FieldDefinitions indexer
            psQuery.QueryFields.Clear();
            for (int fieldCount = 0; fieldCount < TEST_CASE_FIELDS.Length; fieldCount++) {
                psQuery.QueryFields.Add(psFields[TEST_CASE_FIELDS[fieldCount]]);
            }

            // Add fields to sort by
            for (int fieldCount = 0; fieldCount < TEST_CASE_SORT.Length; fieldCount++) {
                psQuery.QuerySortFields.Add(
                psFields[TEST_CASE_SORT[fieldCount]],
                PsSortTypeEnum.psSortTypeAscending);
            }

            psDataList.Execute();
            foreach (DatastoreItem psItem in psDataList.DatastoreItems) {
                foreach (String name in TEST_CASE_FIELDS) {
                    Console.Write("{0}\t", psItem.Fields[name].Value);
                }
                Console.WriteLine();
            }
        }

        private Hashtable CurrentTests()
        {
            // Set up the query.
            Query psQuery = new QueryClass();
            psQuery.CountOnly = false;
            psQuery.SelectionCriteria = QUERY_ACTIVE;
            psQuery.DatastoreItemType = PsDatastoreItemTypeEnum.psDatastoreItemTypeTestCase;

            DatastoreItemList psDataList = new DatastoreItemListClass();
            psDataList.Query = psQuery;
            psDataList.Datastore = m_psDataStore;
            FieldDefinitions psFields = m_psDataStore.FieldDefinitions;

            // Add fields with the FieldDefinitions indexer
            psQuery.QueryFields.Clear();
            for (int fieldCount = 0; fieldCount < TEST_CASE_FIELDS.Length; fieldCount++) {
                psQuery.QueryFields.Add(psFields[TEST_CASE_FIELDS[fieldCount]]);
            }

            // Add fields to sort by
            for (int fieldCount = 0; fieldCount < TEST_CASE_SORT.Length; fieldCount++) {
                psQuery.QuerySortFields.Add(
                psFields[TEST_CASE_SORT[fieldCount]],
                PsSortTypeEnum.psSortTypeAscending);
            }

            Hashtable res = new Hashtable();
            psDataList.Execute();
            foreach (DatastoreItem psItem in psDataList.DatastoreItems) {
                object module = psItem.Fields["Test Module"].Value;
                object suite = psItem.Fields["Test Suite"].Value;
                object testcase = psItem.Fields["TestCase"].Value;
                res[TestKey(module, suite, testcase)] = psItem.Fields["ID"].Value;
            }
            return res;
        }

        // Finds the ID from the Product Path.
        internal static int TreeIDFromPath(Node node, string path)
        {
            char[] separator = {'\\'};
            string[] pathLevelNames = path.Split(separator);
            Node currentNode = node;
            if (path.Trim().Length >= 1 && path.Trim() != "\\") {
                for (int pathCount = 0; pathCount < pathLevelNames.Length; pathCount++) {
                    currentNode = currentNode.Nodes[pathLevelNames[pathCount]];
                }
            }
            return currentNode.ID;
        }

        private void ExportProfile(string testType, string profileName)
        {

            // Set up the query.
            Query psQuery = new QueryClass();
            psQuery.CountOnly = false;
            string query = string.Format(QUERY_PROFILE, testType);
            //string query = QUERY_PROFILE;
            psQuery.SelectionCriteria = query;
            psQuery.DatastoreItemType = PsDatastoreItemTypeEnum.psDatastoreItemTypeTestCase;
            DatastoreItemList psDataList = new DatastoreItemListClass();
            psDataList.Query = psQuery;
            psDataList.Datastore = m_psDataStore;

            // Get the field definitions so we can specify
            // them in the result and sort list.
            FieldDefinitions psFields = m_psDataStore.FieldDefinitions;

            // Add fields with the FieldDefinitions indexer
            psQuery.QueryFields.Clear();
            for (int fieldCount = 0; fieldCount < TEST_CASE_FIELDS.Length; fieldCount++) {
                psQuery.QueryFields.Add(psFields[TEST_CASE_FIELDS[fieldCount]]);
            }

            // Add fields to sort by
            for (int fieldCount = 0; fieldCount < TEST_CASE_SORT.Length; fieldCount++) {
                psQuery.QuerySortFields.Add(psFields[TEST_CASE_SORT[fieldCount]],
                                            PsSortTypeEnum.psSortTypeAscending);
            }

            psDataList.Execute();
            ExportCases(testType, profileName, psDataList.DatastoreItems);
        }

        private void ExportCases(string testType, string profileName, DatastoreItems items)
        {
            XmlTextWriter oo = newXmlProfile(testType, profileName);
            string prevModule = "";
            string prevSuite = "";
            foreach (DatastoreItem psItem in items) {
                object module = psItem.Fields["Test Module"].Value;
                object suite = psItem.Fields["Test Suite"].Value;
                object testcase = psItem.Fields["TestCase"].Value;
                if (module == null || suite == null || testcase == null) {
                    Console.WriteLine("Test case not prepared for automation: {0}", psItem.Fields["ID"].Value);
                    continue;
                }

                if (!module.Equals(prevModule)) {
                    if (prevModule != "") {
                        // special case the first test case
                        oo.WriteEndElement();
                        oo.WriteEndElement();
                    }
                    prevModule = module.ToString();
                    prevSuite = suite.ToString();
                    oo.WriteStartElement("Module");
                    oo.WriteAttributeString("Name", prevModule);
                    oo.WriteStartElement("Suite");
                    oo.WriteAttributeString("Name", prevSuite);
                }
                else if (!suite.Equals(prevSuite)) {
                    prevSuite = suite.ToString();
                    oo.WriteEndElement();
                    oo.WriteStartElement("Suite");
                    oo.WriteAttributeString("Name", prevSuite);
                }
                oo.WriteStartElement("Test");
                oo.WriteAttributeString("Name", testcase.ToString());
                object timeout = psItem.Fields["Test Timeout"].Value;
                if (timeout != null) {
                    oo.WriteAttributeString("Timeout", timeout.ToString());
                }
                object order = psItem.Fields["Order"].Value;
                if (order != null) {
                    oo.WriteAttributeString("Order", order.ToString());
                    int o;
                    //NOTE Magic: the 1000s digit in Order determines the pass for the test.
                    if (Int32.TryParse(order.ToString(), out o) && o / 1000 > 0) {
                        oo.WriteAttributeString("Pass", "" + (o / 1000));
                    }
                }
                object knownFailure = psItem.Fields["Test Known Failure"].Value;
                if (knownFailure != null) {
                    oo.WriteAttributeString("KnownFailure", knownFailure.ToString());
                }
                oo.WriteEndElement();
            }
            if (prevModule != "") {
                oo.WriteEndElement(); // suite
                oo.WriteEndElement(); // module
            }
            oo.WriteEndElement();
            oo.WriteEndDocument();
            oo.Close();
        }

        private static XmlTextWriter newXmlProfile(string testType, string profileName)
        {
            XmlTextWriter oo = new XmlTextWriter(profileName, null);
            oo.Formatting = Formatting.Indented;
            oo.Indentation = 4;
            oo.WriteStartDocument();
            oo.WriteComment("Export of test type " + testType);
            oo.WriteComment("GENERATED FILE. DO NOT EDIT. Add test cases via Product Studio, according to SDN 51");
            oo.WriteStartElement("Profile");
            oo.WriteAttributeString("Name", testType);
            return oo;
        }
    }
}
