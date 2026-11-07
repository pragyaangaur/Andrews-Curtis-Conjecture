import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 249 of the cap-16 certificate: slots 254976 .. 255999 -/
theorem chk_249 : chunkCheck 16 T stdSt 254976 1024 = true := by decide +kernel

end Row16
