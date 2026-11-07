import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 71 of the cap-16 certificate: slots 72704 .. 73727 -/
theorem chk_71 : chunkCheck 16 T stdSt 72704 1024 = true := by decide +kernel

end Row16
