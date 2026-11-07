import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 84 of the cap-16 certificate: slots 86016 .. 87039 -/
theorem chk_84 : chunkCheck 16 T stdSt 86016 1024 = true := by decide +kernel

end Row16
