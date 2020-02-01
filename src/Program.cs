using Antlr4.Runtime;
using Microsoft.Z3;
using QT.Parse;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Runtime.CompilerServices;
using System.Text;

[assembly: CLSCompliant(false)]
[assembly: InternalsVisibleTo("tests")]

namespace QT
{
    internal static class Program
    {
        private static void Main(string[] args)
        {
            Console.OutputEncoding = Encoding.UTF8;

            string example = File.ReadAllText("example.qt");
            Unit unit = AstParser.ParseUnit(example);
            using (var model = new Z3Model())
            {
                var tc = new TypeChecker(model);
                foreach (Def def in unit.Definitions)
                {
                    Console.WriteLine(def);
                    Stopwatch timer = Stopwatch.StartNew();
                    tc.TypeCheck(def);
                    Console.WriteLine("OK in {0} ms", timer.ElapsedMilliseconds);
                    Console.WriteLine();
                }
            }
        }
    }
}
