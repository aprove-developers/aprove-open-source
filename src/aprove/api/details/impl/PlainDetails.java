package aprove.api.details.impl;

import aprove.prooftree.Export.Utility.*;

class PlainDetails extends ExportableDetails<PLAIN_Able> {

    public PlainDetails() {
        super(PLAIN_Able.class);
    }

    @Override
    protected Export_Util exportUtil() {
        return new PLAIN_Util();
    }

    @Override
    protected String details(PLAIN_Able t) {
        return t.toPLAIN();
    }
}
