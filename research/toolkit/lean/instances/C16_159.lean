import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 159 of the cap-16 certificate: slots 162816 .. 163839 -/
theorem chk_159 : chunkCheck 16 T stdSt 162816 1024 = true := by decide +kernel

end Row16
