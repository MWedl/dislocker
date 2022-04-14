//
// Created by michael on 10/24/21.
//

#define _GNU_SOURCE 1

#include <string.h>
#include <dislocker/metadata/metadata.priv.h>
#include <dislocker/encryption/crc32.h>
#include <dislocker/encryption/decrypt.h>
#include <dislocker/ssl_bindings.h>
#include <dislocker/accesses/user_pass/user_pass.h>
#include <dislocker/metadata/vmk.h>

#include "dislocker/xstd/xstdio.h"
#include "dislocker/xstd/xstdlib.h"
#include "dislocker/return_values.h"
#include "dislocker/config.h"
#include "dislocker/dislocker.h"

#include "dislocker/inouts/inouts.h"
#include "dislocker/dislocker.priv.h"


/**
 * Generate a 12 byte nonce. Use a similar algorithm as the original BitLocker implementation.
 * @param priority priority value encoded into nonce
 * @param output
 */
static void generate_nonce(uint16_t priority, uint8_t* output) {
    static uint16_t nonce_counter = 0;

    time_t timestamp;
    ntfs_time_t timestamp_ntfs;
    time(&timestamp);
    utc2ntfs(timestamp, &timestamp_ntfs);

    memcpy(output, &timestamp, 8);
    memcpy(output + 8, &nonce_counter, 2);
    memcpy(output + 10, &priority, 2);

    nonce_counter++;
}


static void random_bytes(uint8_t* buf, size_t length) {
    for(size_t i = 0; i < length; i++) {
        buf[i] = (uint8_t)rand();
    }
}


/**
 * Generate a UUID version 4.
 * @param guid
 */
static void generate_guid(guid_t guid) {
    random_bytes(guid, 16);
    guid[6] = (guid[6] & 0x0F) | 0x40;
    guid[8] = (guid[8] & 0x3F) | 0x80;
}


/**
 * Return the size of bitlocker_information_t->size in bytes
 * @param information
 * @return
 */
static size_t get_information_size(const bitlocker_information_t* information) {
    return (size_t)(information->version == V_SEVEN ? information->size << 4 : information->size);
}

/**
 * Set bitlocker_information_t->size in bytes
 */
static size_t set_information_size(bitlocker_information_t* information, size_t size_in_bytes) {
    size_t size_padded = size_in_bytes;
    size_t size_header = size_in_bytes;
    if (information->version == V_SEVEN) {
        if (size_padded % 16 != 0) {
            size_padded += 16 - (size_padded % 16);
        }
        size_header = size_padded / 16;
    }

    information->size = (uint16_t)size_header;
    information->dataset.size = (uint32_t)(size_in_bytes - 0x40);
    information->dataset.copy_size = information->dataset.size;

    return size_padded;
}

/**
 * Similar to get_header_safe but does not perform allocations
 * @param data
 * @param output
 * @return
 */
static int get_payload(void* data, void** output, size_t* output_size) {
    if (!data || !output) {
        return FALSE;
    }

    datum_header_safe_t header;
    if(!get_header_safe(data, &header)) {
        return FALSE;
    }

    size_t header_size = datum_value_types_prop[header.value_type].size_header;
    if(header.datum_size <= header_size) {
        return FALSE;
    }

    *output = data + header_size;
    if (output_size != NULL) {
        *output_size = header.datum_size - header_size;
    }
    return TRUE;
}

static int datum_aes_ccm_new(const datum_key_t* inner, const datum_key_t* key, const uint8_t* nonce, datum_aes_ccm_t** output) {
    if (!inner || !nonce || !output || !key) {
        return FALSE;
    }

    datum_aes_ccm_t header = {
            .header = {
                    .datum_size = sizeof(datum_aes_ccm_t) + inner->header.datum_size,
                    .entry_type = DATUMS_ENTRY_NONE,
                    .value_type = DATUMS_VALUE_AES_CCM,
                    .error_status = 1,
            },
    };
    memcpy(header.nonce, nonce, 12);

    unsigned char* key_bytes = NULL;
    size_t key_size;
    void* inner_encrypted = NULL;
    if (!get_payload((void*)key, (void**)&key_bytes, &key_size) ||
        !encrypt_key(
                (unsigned char*)inner, inner->header.datum_size,
                key_bytes, (unsigned int)key_size * 8,
                header.nonce, header.mac,
                &inner_encrypted)) {
        return FALSE;
    }

    *output = dis_malloc(header.header.datum_size);
    memcpy(*output, &header, sizeof(datum_aes_ccm_t));
    memcpy((void*)(*output) + sizeof(datum_aes_ccm_t), inner_encrypted, inner->header.datum_size);

    dis_free(inner_encrypted);

    return TRUE;
}

static int datum_aes_ccm_decrypt(const datum_aes_ccm_t* datum, const datum_key_t* key, datum_key_t** output) {
    if (!datum || !key || !output) {
        return FALSE;
    }

    unsigned char* key_bytes = NULL;
    size_t key_size;
    unsigned char* input = NULL;
    size_t input_size;
    if (!get_payload((void*)key, (void**)&key_bytes, &key_size) ||
        !get_payload((void*)datum, (void**)&input, &input_size)) {
        return FALSE;
    }

    return decrypt_key(
            input, (unsigned int)input_size,
            datum->mac, datum->nonce,
            key_bytes, (unsigned int)key_size * 8,
            (void**)output);
}

static int datum_aes_ccm_reencrypt(const datum_aes_ccm_t* datum, const datum_key_t* key_old, const datum_key_t* key_new, datum_aes_ccm_t** output) {
    if (!datum || !key_old || !key_new || !output) {
        return FALSE;
    }

    // Decrypt with old key
    datum_key_t* datum_inner = NULL;
    if (!datum_aes_ccm_decrypt(datum, key_old, &datum_inner)) {
        return FALSE;
    }

    // Re-encrypt with new key
    if (!datum_aes_ccm_new(datum_inner, key_new, datum->nonce, output)) {
        dis_free(datum_inner);
        return FALSE;
    }

    (*output)->header.entry_type = datum->header.entry_type;
    (*output)->header.value_type = datum->header.value_type;
    (*output)->header.error_status = datum->header.error_status;
    return TRUE;
}


/**
 * Create a datum for a user password key protector.
 * Contains the VMK encrypted with a key derived from the user password.
 * @param password
 * @param output
 * @param output_size
 * @return
 */
static int user_password_datum_new(const char* password, const datum_key_t* vmk, datum_vmk_t** output) {
    if (!password || !vmk || !output) {
        return FALSE;
    }

    uint8_t password_salt[16];
    random_bytes(password_salt, 16);

    // derive key from password
    uint8_t derived_key[32];
    if (!user_key((uint8_t*)password, password_salt, derived_key)) {
        return FALSE;
    }
    datum_key_t stretch_inner_header = {
            .header = {
                    .datum_size = sizeof(datum_key_t) + 32,
                    .entry_type = DATUMS_ENTRY_NONE,
                    .value_type = DATUMS_VALUE_KEY,
                    .error_status = 0,
            },
            .algo = USER_KEY,
            .padd = 0,
    };
    uint8_t stretch_inner[stretch_inner_header.header.datum_size];
    memcpy(stretch_inner, &stretch_inner_header, sizeof(datum_key_t));
    memcpy((void*)stretch_inner + sizeof(datum_key_t), derived_key, 32);


    // encrypt VMK with derived_key
    uint8_t encrypted_vmk_nonce[12];
    generate_nonce(0, encrypted_vmk_nonce);
    datum_aes_ccm_t* encrypted_vmk = NULL;
    if (!datum_aes_ccm_new(vmk, (datum_key_t*)stretch_inner, encrypted_vmk_nonce, &encrypted_vmk)) {
        return FALSE;
    }

    // encrypt derived_key with VMK
    uint8_t stretch_aesccm_nonce[12];
    generate_nonce(0, stretch_aesccm_nonce);
    datum_aes_ccm_t* stretch_aesccm = NULL;
    if (!datum_aes_ccm_new(
            (datum_key_t*)stretch_inner,
            vmk, stretch_aesccm_nonce,
            &stretch_aesccm)) {
        dis_free(encrypted_vmk);
        return FALSE;
    }


    datum_stretch_key_t stretch_key_datum_header = {
            .header = {
                    .datum_size = sizeof(datum_stretch_key_t) + stretch_aesccm->header.datum_size,  // Expected length: 108
                    .entry_type = DATUMS_ENTRY_NONE,
                    .value_type = DATUMS_VALUE_STRETCH_KEY,
                    .error_status = 1,
            },
            .algo = STRETCH_KEY_2,
            .padd = 0,
    };
    memcpy(stretch_key_datum_header.salt, password_salt, 16);

    datum_vmk_t password_datum_header = {
            .header = {
                    .datum_size = (uint16_t)(sizeof(datum_vmk_t) + encrypted_vmk->header.datum_size + stretch_key_datum_header.header.datum_size),
                    .entry_type = DATUMS_ENTRY_VMK,
                    .value_type = DATUMS_VALUE_VMK,
                    .error_status = 1
            },
    };
    generate_guid(password_datum_header.guid);
    generate_nonce(0x2000, password_datum_header.nonce);


    // Build final datum structure
    *output = dis_malloc(password_datum_header.header.datum_size);
    void* output_buf = *output;
    memcpy(output_buf, &password_datum_header, sizeof(password_datum_header));
    output_buf += sizeof(password_datum_header);
    memcpy(output_buf, &stretch_key_datum_header, sizeof(stretch_key_datum_header));
    output_buf += sizeof(stretch_key_datum_header);
    memcpy(output_buf, stretch_aesccm, stretch_aesccm->header.datum_size);
    output_buf += stretch_aesccm->header.datum_size;
    memcpy(output_buf, encrypted_vmk, encrypted_vmk->header.datum_size);

    dis_free(encrypted_vmk);
    dis_free(stretch_aesccm);

    return TRUE;
}


static int datum_clearkey_new(const datum_key_t* vmk, datum_vmk_t** output) {
    // Generate clear key
    datum_key_t clearkey_header = {
            .header = {
                    .datum_size = sizeof(datum_key_t) + 32,
                    .entry_type = DATUMS_ENTRY_NONE,
                    .value_type = DATUMS_VALUE_KEY,
                    .error_status = 1,
            },
            .algo = AES_CCM_256_0,
            .padd = 0,
    };
    uint8_t clearkey_bytes[clearkey_header.header.datum_size];
    memcpy(clearkey_bytes, &clearkey_header, sizeof(datum_key_t));
    random_bytes(clearkey_bytes + sizeof(datum_key_t), 32);
    datum_key_t* clearkey = (datum_key_t*)clearkey_bytes;

    // encrypt VMK with clear key
    uint8_t encrypted_vmk_nonce[12];
    generate_nonce(0, encrypted_vmk_nonce);
    datum_aes_ccm_t* encrypted_vmk = NULL;
    if (!datum_aes_ccm_new(vmk, clearkey, encrypted_vmk_nonce, &encrypted_vmk)) {
        return FALSE;
    }


    datum_vmk_t datum_clearkey_header = {
            .header = {
                    .datum_size = (uint16_t)(sizeof(datum_vmk_t) + clearkey->header.datum_size + encrypted_vmk->header.datum_size),
                    .entry_type = DATUMS_ENTRY_VMK,
                    .value_type = DATUMS_VALUE_VMK,
                    .error_status = 0x105,
            },
    };
    generate_guid(datum_clearkey_header.guid);
    memcpy(datum_clearkey_header.nonce, encrypted_vmk_nonce, 12);

    // Build final datum
    *output = dis_malloc(datum_clearkey_header.header.datum_size);
    void* output_buf = *output;
    memcpy(output_buf, &datum_clearkey_header, sizeof(datum_vmk_t));
    output_buf += sizeof(datum_vmk_t);
    memcpy(output_buf, clearkey, clearkey->header.datum_size);
    output_buf += clearkey->header.datum_size;
    memcpy(output_buf, encrypted_vmk, encrypted_vmk->header.datum_size);

    dis_free(encrypted_vmk);

    return TRUE;
}

/**
 * Append a datum to a metadata block.
 * Does not modify the existing metadata.
 * Returns a copy of the metadata block including the new datum appended at the end.
 * @param information_old
 * @param datum
 * @param output
 * @return
 */
static int metadata_append_datum(const bitlocker_information_t* information_old, const datum_header_safe_t* datum, bitlocker_information_t** output) {
    if (!information_old || !datum || !output) {
        return FALSE;
    }

    dis_printf(L_DEBUG, "Appending datum to metadata\n");
    print_one_datum(L_DEBUG, (void*)datum);

    // Create new metadata
    size_t size_old = information_old->dataset.size + 0x40;
    size_t size_new = size_old + datum->datum_size;
    size_t size_new_padded = size_new;
    if (information_old->version == V_SEVEN && size_new % 16 != 0) {
        size_new_padded += 16 - (size_new % 16);
    }

    bitlocker_information_t* information_new = dis_malloc(size_new_padded);

    // Add new password datum
    memcpy(information_new, information_old, size_old);
    memcpy((void*)information_new + size_old, datum, datum->datum_size);
    memset((void*)information_new + size_new, 0, size_new_padded - size_new);

    // Update size
    set_information_size(information_new, size_new);

    *output = information_new;
    return TRUE;
}

/**
 * Add a password key-protector to metadata entries
 * @param password
 * @return
 */
static int add_password_entry(dis_metadata_t metadata, const char* password, const datum_key_t* vmk) {
    if (!metadata || !password || !vmk) {
        return FALSE;
    }

    dis_printf(L_INFO, "Adding password datum for \"%s\"\n", password);

    // Create new datum for password
    datum_vmk_t* password_datum = NULL;
    if (!user_password_datum_new(password, vmk, &password_datum)) {
        return FALSE;
    }

    // Create new metadata
    bitlocker_information_t* information_old = metadata->information;
    bitlocker_information_t* information_new = NULL;
    if (!metadata_append_datum(information_old, (datum_header_safe_t*)password_datum, &information_new)) {
        dis_free(password_datum);
        return FALSE;
    }

    // Replace pointers to metadata
    metadata->information = information_new;
    metadata->dataset = &information_new->dataset;

    // Cleanup
    dis_free(password_datum);
    dis_free(information_old);

    return TRUE;
}


static int add_clearkey_entry(dis_metadata_t metadata, const datum_key_t* vmk) {
    if (!metadata || !vmk) {
        return FALSE;
    }

    dis_printf(L_INFO, "Adding clear key datum\n");

    // Create clearkey datum
    datum_vmk_t* datum_clearkey = NULL;
    if (!datum_clearkey_new(vmk, &datum_clearkey)) {
        return FALSE;
    }

    // Create new metadata
    bitlocker_information_t* information_old = metadata->information;
    bitlocker_information_t* information_new = NULL;
    if (!metadata_append_datum(information_old, (datum_header_safe_t*)datum_clearkey, &information_new)) {
        dis_free(datum_clearkey);
        return FALSE;
    }

    // Replace pointers to metadata
    metadata->information = information_new;
    metadata->dataset = &information_new->dataset;

    // Cleanup
    dis_free(datum_clearkey);
    dis_free(information_old);

    return TRUE;
}

/**
 * Change the VMK.
 * When the old VMK is provided, metadata datums are decrypted with the old VMK and re-encrypted with the new VMK.
 * Else, all entries encrypted with the old VMK are removed.
 * @param metadata
 * @param vmk_new
 * @param vmk_old
 * @param fvek
 * @return
 */
static int change_vmk(dis_metadata_t metadata, const datum_key_t* vmk_new, const datum_key_t* vmk_old, const datum_key_t* fvek) {
    if (!metadata || !vmk_new || !fvek) {
        return FALSE;
    }

    dis_printf(L_INFO, "Changing the VMK. New VMK:\n");
    print_one_datum(L_INFO, (void*)vmk_new);

    // Initialize new metadata headers
    bitlocker_information_t* information_new = dis_malloc(get_information_size(metadata->information));
    memcpy(information_new, metadata->information, sizeof(bitlocker_information_t));
    size_t information_size = sizeof(bitlocker_information_t);

    // Iterate over all datums
    datum_header_safe_t* datum = NULL;
    while (get_next_datum(metadata, UINT16_MAX, UINT16_MAX, datum, (void**)&datum)) {
        datum_header_safe_t* datum_new = NULL;

        if (datum->entry_type == DATUMS_ENTRY_FVEK && datum->value_type == DATUMS_VALUE_AES_CCM) {
            // Encrypt FVEK with VMK
            uint8_t nonce[12];
            generate_nonce(0, nonce);
            if (!datum_aes_ccm_new(fvek, vmk_new, nonce, (datum_aes_ccm_t **)&datum_new)) {
                return FALSE;
            }
            datum_new->entry_type = DATUMS_ENTRY_FVEK;
        } else if (datum->entry_type == DATUMS_ENTRY_VMK && datum->value_type == DATUMS_VALUE_VMK) {
            if (!vmk_old) {
                dis_printf(L_WARNING, "Cannot re-encrypt datum, because the old VMK is not known. Removing it.\n");
                print_one_datum(L_WARNING, datum);
                continue;
            } else {
                // Re-encrypt datum with new VMK
                if (!datum_aes_ccm_reencrypt((datum_aes_ccm_t*)datum, vmk_old, vmk_new, (datum_aes_ccm_t**)&datum_new)) {
                    dis_free(information_new);
                    return FALSE;
                }
            }
        } else {
            // Other datum: copy to new metadata
            dis_printf(L_DEBUG, "Copying datum from old metadata to new metadata.\n");
            print_one_datum(L_DEBUG, datum);

            datum_new = dis_malloc(datum->datum_size);
            memcpy(datum_new, datum, datum->datum_size);
        }

        // append new datum
        if (datum_new != NULL) {
            memcpy((void*)information_new + information_size, datum_new, datum_new->datum_size);
            information_size += datum_new->datum_size;
            dis_free(datum_new);
        }
    }

    // Set size
    set_information_size(information_new, information_size);

    // Set new metadata
    dis_free(metadata->information);
    metadata->information = information_new;
    metadata->dataset = &information_new->dataset;

    return TRUE;
}


/**
 * Create the metadata validation datum containing an encrypted SHA256 hash of metadata
 * @param datum
 * @param metadata
 * @param metadata_size
 * @return
 */
static int create_validation_datum(const void* metadata, size_t metadata_size, datum_key_t* vmk, datum_aes_ccm_t** output) {
    if (!vmk) {
        dis_printf(L_WARNING, "VMK not available. Cannot create metadata validation datum.\n");
        return FALSE;
    }

    // calculate hash of metadata
    uint8_t sha256_hash[32];
    SHA256(metadata, metadata_size, sha256_hash);

    // Build inner datum containing hash
    datum_key_t hash_datum_header = {
            .header = {
                    .datum_size = sizeof(datum_key_t) + 32,
                    .entry_type = DATUMS_ENTRY_NONE,
                    .value_type = DATUMS_VALUE_KEY,
                    .error_status = 0
            },
            .algo = HASH_256,
            .padd = 0
    };
    uint8_t hash_datum[hash_datum_header.header.datum_size];
    memcpy(hash_datum, &hash_datum_header, sizeof(datum_key_t));
    memcpy(hash_datum + sizeof(datum_key_t), sha256_hash, 32);


    // Encrypt inner datum with VMK
    uint8_t nonce[12];
    generate_nonce(0, nonce);
    return datum_aes_ccm_new((datum_key_t*)hash_datum, vmk, nonce, output);
}


/**
 * Serialize metadata to bytes which can be written to disk.
 * Calculates and appends checksums of metadata.
 */
static int serialize_metadata(const bitlocker_information_t* metadata, datum_key_t* vmk, void** output, size_t* output_size) {
    // TODO: check if size always fills up to 65536
    *output_size = 65536;

    // Check metadata size
    size_t metadata_size = get_information_size(metadata);
    if (metadata_size > 65536 - sizeof(bitlocker_validations_t) - sizeof(datum_aes_ccm_t) - sizeof(datum_key_t) - 32) {
        dis_printf(L_ERROR, "Metadata too large. Cannot write to disk.\n");
        return FALSE;
    }

    *output = dis_malloc(*output_size);

    // Metadata header is stored in contiguous memory as-is using the same structures as on-disk
    // We can directly copy it
    memcpy(*output, metadata, metadata_size);

    // Re-calculate CRC32 checksum of metadata
    bitlocker_validations_t validation_header = {
            .size = (uint16_t)(*output_size - metadata_size),
            .version = 2,
            .crc32 = crc32((unsigned char*)metadata, (unsigned int)metadata_size),
    };
    memcpy(*output + metadata_size, &validation_header, sizeof(validation_header));

    // Re-calculate encrypted SHA256 hash datum of metadata
    size_t zero_padding_size = validation_header.size - sizeof(bitlocker_validations_t);
    datum_aes_ccm_t* validation_datum = NULL;
    if (!create_validation_datum(metadata, metadata_size, vmk, &validation_datum)) {
        dis_free(*output);
        return FALSE;
    }
    memcpy(*output + metadata_size + sizeof(bitlocker_validations_t), validation_datum, validation_datum->header.datum_size);
    zero_padding_size -= validation_datum->header.datum_size;
    dis_free(validation_datum);

    // pad up to validation.size with 0
    memset(*output + *output_size - zero_padding_size, 0, zero_padding_size);


    // ignore EOW (only used when testing volume before encryption? and not on actually encrypted volumes)

    dis_printf(L_DEBUG, "Serialized BitLocker metadata: \n");
    hexdump(L_DEBUG, *output, *output_size - zero_padding_size);

    return TRUE;
}


/**
 * Write BitLocker headers to disk.
 * This includes the volume header and three redundant metadata blocks.
 * @return
 */
static int write_headers(dis_context_t dis_ctx) {
    void* metadata = NULL;
    size_t metadata_size;
    if (!serialize_metadata(dis_ctx->metadata->information, dis_ctx->io_data.vmk, &metadata, &metadata_size)) {
        return FALSE;
    }

    int fd = dis_ctx->fve_fd;

    // Write volume header
    dis_printf(L_DEBUG, "Writing volume header to disk (address 0).\n");
    dis_lseek(fd, dis_ctx->cfg.offset + 0, SEEK_SET);
    dis_write(fd, dis_ctx->metadata->volume_header, sizeof(volume_header_t));

    // Write redundant metadata blocks
    for (int i = 0; i < 3; i++) {
        dis_printf(L_DEBUG, "Writing metadata block to disk (address %lld).\n", dis_ctx->metadata->virt_region[i].addr);
        off_t metadata_offset = dis_ctx->cfg.offset + (off_t)dis_ctx->metadata->virt_region[i].addr;
        dis_lseek(fd, metadata_offset, SEEK_SET);
        dis_write(fd, metadata, metadata_size);
    }

    return TRUE;
}


int dis_init_arguments(int argc, char* argv[], dis_context_t* dis_ctx) {
    // TODO: add command line options for specifying clear key and new password + update usage
    // Check parameters number
    if(argc < 2) {
        dis_usage();
        return FALSE;
    }

    // Get command line options
    *dis_ctx = dis_new();
    int param_idx = dis_getopts(*dis_ctx, argc, argv);

    // Check we have a volume path given and if not, take the first non-argument as the volume path
    void* volume_path = NULL;
    dis_getopt(*dis_ctx, DIS_OPT_VOLUME_PATH, (void**) &volume_path);
    if(volume_path == NULL) {
        if(param_idx >= argc || param_idx <= 0) {
            dis_printf(L_CRITICAL, "Error, no volume path given. Abort.\n");
            dis_free(*dis_ctx);
            *dis_ctx = NULL;
            return FALSE;
        }

        dis_printf(L_DEBUG, "Setting the volume path to %s.\n", argv[param_idx]);
        dis_setopt(*dis_ctx, DIS_OPT_VOLUME_PATH, argv[param_idx]);
        param_idx++;
    }

    // Initialize dislocker
    if(dis_initialize(*dis_ctx) != DIS_RET_SUCCESS) {
        dis_printf(L_CRITICAL, "Can't initialize dislocker. Abort.\n");
        return FALSE;
    }

    return TRUE;
}


int main(int argc, char* argv[]) {
    int ret = EXIT_SUCCESS;

    // TODO: use a better random generator
    srand((unsigned int)clock());

    dis_context_t dis_ctx;
    if (!dis_init_arguments(argc, argv, &dis_ctx)) {
        return EXIT_FAILURE;
    }

    if (dis_ctx->io_data.vmk == NULL) {
        // Generate new VMK
        datum_key_t vmk_new_header = {
                .header = {
                        .datum_size = sizeof(datum_key_t) + 32,
                        .entry_type = DATUMS_ENTRY_NONE,
                        .value_type = DATUMS_VALUE_KEY,
                        .error_status = 0,
                },
                .algo = VMK,
                .padd = 0,
        };
        datum_key_t* vmk_new = dis_malloc(vmk_new_header.header.datum_size);
        memcpy(vmk_new, &vmk_new_header, sizeof(datum_key_t));
        random_bytes((void*)vmk_new + sizeof(datum_key_t), 32);
        dis_ctx->io_data.vmk = vmk_new;

        if (!change_vmk(dis_ctx->metadata, dis_ctx->io_data.vmk, NULL, dis_ctx->io_data.fvek)) {
            dis_destroy(dis_ctx);
            return EXIT_FAILURE;
        }
    }

    // Add clearkey and password
    if (!add_password_entry(dis_ctx->metadata, "newpwd", dis_ctx->io_data.vmk) ||
        !add_clearkey_entry(dis_ctx->metadata, dis_ctx->io_data.vmk) ||
        !write_headers(dis_ctx)
            ) {
        ret = EXIT_FAILURE;
    }

    // Destroy dislocker structures
    dis_destroy(dis_ctx);

    return ret;
}
