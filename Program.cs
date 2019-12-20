using Antlr4.Runtime;
using Microsoft.Z3;
using QT.Parse;
using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

[assembly: CLSCompliant(false)]

namespace QT
{
    internal static class Program
    {
        private static void Main(string[] args)
        {
            Console.OutputEncoding = Encoding.UTF8;

            string example = File.ReadAllText("example.qt");
            Unit unit = AstParser.ParseUnit(example);
            using (var tc = new TypeChecker())
            {
                foreach (Def def in unit.Definitions)
                {
                    Console.WriteLine(def);
                    tc.TypeCheck(def);
                    Console.WriteLine("OK");
                    Console.WriteLine();
                }
            }
        }
    }
}
