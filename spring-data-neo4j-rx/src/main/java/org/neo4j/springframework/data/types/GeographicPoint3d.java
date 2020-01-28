/*
 * Copyright (c) 2019-2020 "Neo4j,"
 * Neo4j Sweden AB [https://neo4j.com]
 *
 * This file is part of Neo4j.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.neo4j.springframework.data.types;

import org.apiguardian.api.API;

/**
 * @author Michael J. Simons
 * @since 1.0
 */
@API(status = API.Status.STABLE, since = "1.0")
public final class GeographicPoint3d extends AbstractPoint {

    GeographicPoint3d(Coordinate coordinate, Integer srid) {
        super(coordinate, srid);
    }

    public GeographicPoint3d(double latitude, double longitude, double height) {
        super(new Coordinate(longitude, latitude, height), 4979);
    }

    public double getLongitude() {
        return coordinate.getX();
    }

    public double getLatitude() {
        return coordinate.getY();
    }

    public double getHeight() {
        return coordinate.getZ();
    }

    @Override
    public String toString() {
        return "GeographicPoint3d{" +
            "longitude=" + getLongitude() +
            ", latitude=" + getLatitude() +
            ", height=" + getHeight() +
            ", srid=" + getSrid() +
            '}';
    }
}
