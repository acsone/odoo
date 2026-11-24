# Copyright 2025 ACSONE SA/NV (<http://acsone.eu>)
# License AGPL-3.0 or later (http://www.gnu.org/licenses/agpl.html).
import logging

from odoo import SUPERUSER_ID, api

_logger = logging.getLogger(__name__)


def migrate(cr, version):
    """
    Get values from temp table and fill it in new res.partner user_id field with ORM.
    :param env:
    :return:
    """
    env = api.Environment(cr, SUPERUSER_ID, {})
    all_partners = env["res.partner"].with_context(active_test=True).search([])
    get_user_query = """
    SELECT partner_id, user_id
    FROM mig_res_partner_user_id_company_dependent;
    """
    env.cr.execute(get_user_query)
    partner_user = {
        data.get("partner_id"): data.get("user_id") for data in env.cr.dictfetchall()
    }
    for company in env["res.company"].search([]):
        partners = all_partners.with_company(company.id)
        for partner in partners:
            partner.write(
                {
                    "user_id": partner_user.get(partner.id),
                }
            )
    delete_query = "DROP TABLE mig_res_partner_user_id_company_dependent;"
    env.cr.execute(delete_query)
