import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 111 of the cap-16 certificate: slots 113664 .. 114687 -/
theorem chk_111 : chunkCheck 16 T stdSt 113664 1024 = true := by decide +kernel

end Row16
