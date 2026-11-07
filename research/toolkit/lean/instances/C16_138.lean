import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 138 of the cap-16 certificate: slots 141312 .. 142335 -/
theorem chk_138 : chunkCheck 16 T stdSt 141312 1024 = true := by decide +kernel

end Row16
