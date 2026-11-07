import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 126 of the cap-16 certificate: slots 129024 .. 130047 -/
theorem chk_126 : chunkCheck 16 T stdSt 129024 1024 = true := by decide +kernel

end Row16
