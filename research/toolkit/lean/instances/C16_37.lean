import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 37 of the cap-16 certificate: slots 37888 .. 38911 -/
theorem chk_37 : chunkCheck 16 T stdSt 37888 1024 = true := by decide +kernel

end Row16
