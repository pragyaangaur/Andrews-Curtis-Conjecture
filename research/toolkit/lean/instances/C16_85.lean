import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 85 of the cap-16 certificate: slots 87040 .. 88063 -/
theorem chk_85 : chunkCheck 16 T stdSt 87040 1024 = true := by decide +kernel

end Row16
