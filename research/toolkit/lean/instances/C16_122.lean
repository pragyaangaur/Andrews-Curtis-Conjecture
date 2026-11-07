import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 122 of the cap-16 certificate: slots 124928 .. 125951 -/
theorem chk_122 : chunkCheck 16 T stdSt 124928 1024 = true := by decide +kernel

end Row16
