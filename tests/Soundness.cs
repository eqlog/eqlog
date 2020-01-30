using QT;
using Xunit;

namespace Tests
{
    public class Soundness
    {
        [Fact]
        public void TestTrueIsNotFalse()
        {
            using Z3Model m = new Z3Model();
            EmptyCtx n1 = m.EmptyCtx();
            BoolTy n2 = m.Bool(n1);
            TrueTm n3 = m.True(n1);
            FalseTm n4 = m.False(n1);
            ComprehensionCtx n6 = m.Comprehension(n1, n2);
            BoolTy n8 = m.Bool(n6);
            ProjTm n9 = m.ProjTm(n6);
            TrueTm n10 = m.True(n6);
            ComprehensionCtx n11 = m.Comprehension(n6, n8);
            ProjTm n14 = m.ProjTm(n11);
            IdMorph n15 = m.IdMorph(n6);
            ExtensionMorph n16 = m.Extension(n15, n10, n8);
            FalseTm n17 = m.False(n6);
            ExtensionMorph n18 = m.Extension(n15, n17, n8);
            IdMorph n24 = m.IdMorph(n1);
            ExtensionMorph n25 = m.Extension(n24, n3, n2);
            CompMorph n26 = m.Compose(n18, n25);
            CompMorph n27 = m.Compose(n16, n25);
            ExtensionMorph n30 = m.Extension(n24, n4, n2);
            Assert.False(m.TmEq(n10, n17));
        }
    }
}
