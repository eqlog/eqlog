using System.Runtime.CompilerServices;

namespace QT
{
    internal abstract class ModelObject
    {
        public ModelObject(uint modelId)
            => Id = modelId;

        public uint Id { get; }

        internal static ConditionalWeakTable<ModelObject, string> DbgInfo { get; }
            = new ConditionalWeakTable<ModelObject, string>();

        public string? GetDebugInfo()
            => DbgInfo.TryGetValue(this, out string? s) ? s : null;

        public override string ToString()
            => GetDebugInfo() ?? $"#{Id:x8}";
    }

    internal class ModelCtx : ModelObject
    {
        public ModelCtx(uint modelId) : base(modelId)
        {
        }
    }

    internal class CtxMorphism : ModelObject
    {
        public CtxMorphism(uint modelId, ModelCtx from, ModelCtx to) : base(modelId)
        {
            From = from;
            To = to;
        }

        public ModelCtx From { get; }
        public ModelCtx To { get; }
    }

    internal class Ty : ModelObject
    {
        public Ty(uint modelId, ModelCtx context) : base(modelId)
            => Context = context;

        public ModelCtx Context { get; }
    }

    internal class Tm : ModelObject
    {
        public Tm(uint modelId, Ty ty) : base(modelId)
            => Ty = ty;

        public Ty Ty { get; }
        public ModelCtx Context => Ty.Context;
    }
}
